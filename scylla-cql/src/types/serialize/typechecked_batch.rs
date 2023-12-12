use std::borrow::Cow;
use std::sync::Arc;

use bytes::BufMut;

use crate::_macro_internal::RowSerializationContext;
use crate::frame::value::SerializeValuesError;

use super::batch::{BatchValues, BatchValuesIterator};
use super::row::SerializedValues;
use super::{RowWriter, SerializationError};

pub type SerializedResult<'a> = Result<Cow<'a, SerializedValues>, SerializationError>;

/// Represents List of ValueList for Batch statement
pub trait TypecheckedBatchValues {
    /// For some unknown reason, this type, when not resolved to a concrete type for a given async function,
    /// cannot live across await boundaries while maintaining the corresponding future `Send`, unless `'r: 'static`
    ///
    /// See <https://github.com/scylladb/scylla-rust-driver/issues/599> for more details
    type TypecheckedBatchValuesIter<'r>: TypecheckedBatchValuesIterator<'r>
    where
        Self: 'r;
    fn batch_values_iter(&self) -> Self::TypecheckedBatchValuesIter<'_>;
}

/// An iterator-like for `ValueList`
///
/// An instance of this can be easily obtained from `IT: Iterator<Item: ValueList>`: that would be
/// `BatchValuesIteratorFromIterator<IT>`
///
/// It's just essentially making methods from `ValueList` accessible instead of being an actual iterator because of
/// compiler limitations that would otherwise be very complex to overcome.
/// (specifically, types being different would require yielding enums for tuple impls)
pub trait TypecheckedBatchValuesIterator<'a> {
    fn next_serialized(&mut self) -> Option<SerializedResult<'a>>;
    fn write_next_to_request(
        &mut self,
        buf: &mut impl BufMut,
    ) -> Option<Result<(), SerializationError>>;
    fn skip_next(&mut self) -> Option<()>;
    fn count(mut self) -> usize
    where
        Self: Sized,
    {
        let mut count = 0;
        while self.skip_next().is_some() {
            count += 1;
        }
        count
    }
}

/// Implements `BatchValuesIterator` from an `Iterator` over references to things that implement `SerializeRow`
///
/// Essentially used internally by this lib to provide implementers of `BatchValuesIterator` for cases
/// that always serialize the same concrete `SerializeRow` type
pub struct TypecheckedBatchValuesIteratorFromIterator<IT: Iterator> {
    it: IT,
}

impl<'r, 'a: 'r, IT> TypecheckedBatchValuesIterator<'r>
    for TypecheckedBatchValuesIteratorFromIterator<IT>
where
    IT: Iterator<Item = &'a SerializedValues>,
{
    fn next_serialized(&mut self) -> Option<SerializedResult<'a>> {
        self.it.next().map(|sv| Ok(Cow::Borrowed(sv)))
    }
    fn write_next_to_request(
        &mut self,
        buf: &mut impl BufMut,
    ) -> Option<Result<(), SerializationError>> {
        self.it.next().map(|sv| Ok(sv.write_to_request(buf)))
    }
    fn skip_next(&mut self) -> Option<()> {
        self.it.next().map(|_| ())
    }
}

impl<'a, IT> From<IT> for TypecheckedBatchValuesIteratorFromIterator<IT>
where
    IT: Iterator<Item = &'a SerializedValues>,
{
    fn from(it: IT) -> Self {
        TypecheckedBatchValuesIteratorFromIterator { it }
    }
}

//
// BatchValues impls
//

/// Implements `BatchValues` from an `Iterator` over references to things that implement `SerializeRow`
///
/// This is to avoid requiring allocating a new `Vec` containing all the `SerializeRow`s directly:
/// with this, one can write:
/// `session.batch(&batch, BatchValuesFromIter::from(lines_to_insert.iter().map(|l| &l.value_list)))`
/// where `lines_to_insert` may also contain e.g. data to pick the statement...
///
/// The underlying iterator will always be cloned at least once, once to compute the length if it can't be known
/// in advance, and be re-cloned at every retry.
/// It is consequently expected that the provided iterator is cheap to clone (e.g. `slice.iter().map(...)`).
pub struct TypecheckedBatchValuesFromIter<'a, IT> {
    it: IT,
    _spooky: std::marker::PhantomData<&'a ()>,
}

impl<'a, IT> TypecheckedBatchValuesFromIter<'a, IT>
where
    IT: Iterator<Item = &'a SerializedValues> + Clone,
{
    pub fn new(into_iter: impl IntoIterator<IntoIter = IT>) -> Self {
        Self {
            it: into_iter.into_iter(),
            _spooky: std::marker::PhantomData,
        }
    }
}

impl<'a, IT> From<IT> for TypecheckedBatchValuesFromIter<'a, IT>
where
    IT: Iterator<Item = &'a SerializedValues> + Clone,
{
    fn from(it: IT) -> Self {
        Self::new(it)
    }
}

impl<'a, IT> TypecheckedBatchValues for TypecheckedBatchValuesFromIter<'a, IT>
where
    IT: Iterator<Item = &'a SerializedValues> + Clone,
{
    type TypecheckedBatchValuesIter<'r> = TypecheckedBatchValuesIteratorFromIterator<IT> where Self: 'r;
    fn batch_values_iter(&self) -> Self::TypecheckedBatchValuesIter<'_> {
        self.it.clone().into()
    }
}

// Implement BatchValues for slices of SerializeRow types
impl TypecheckedBatchValues for [SerializedValues] {
    type TypecheckedBatchValuesIter<'r> = TypecheckedBatchValuesIteratorFromIterator<std::slice::Iter<'r, SerializedValues>> where Self: 'r;
    fn batch_values_iter(&self) -> Self::TypecheckedBatchValuesIter<'_> {
        self.iter().into()
    }
}

// Implement BatchValues for Vec<SerializeRow>
impl TypecheckedBatchValues for Vec<SerializedValues> {
    type TypecheckedBatchValuesIter<'r> = TypecheckedBatchValuesIteratorFromIterator<std::slice::Iter<'r, SerializedValues>> where Self: 'r;
    fn batch_values_iter(&self) -> Self::TypecheckedBatchValuesIter<'_> {
        TypecheckedBatchValues::batch_values_iter(self.as_slice())
    }
}

// Here is an example implementation for (T0, )
// Further variants are done using a macro
impl TypecheckedBatchValues for (SerializedValues,) {
    type TypecheckedBatchValuesIter<'r> = TypecheckedBatchValuesIteratorFromIterator<std::iter::Once<&'r SerializedValues>> where Self: 'r;
    fn batch_values_iter(&self) -> Self::TypecheckedBatchValuesIter<'_> {
        std::iter::once(&self.0).into()
    }
}

// Every &impl BatchValues should also implement BatchValues
impl<'a, T: TypecheckedBatchValues + ?Sized> TypecheckedBatchValues for &'a T {
    type TypecheckedBatchValuesIter<'r> = <T as TypecheckedBatchValues>::TypecheckedBatchValuesIter<'r> where Self: 'r;
    fn batch_values_iter(&self) -> Self::TypecheckedBatchValuesIter<'_> {
        <T as TypecheckedBatchValues>::batch_values_iter(*self)
    }
}

// Converting BatchValues to TypecheckedBatchValues

pub struct TypecheckedBatchValuesIteratorFromBatchValuesIterator<BVI, CTX> {
    bvi: BVI,
    ctx: CTX,
}

impl<BVI, CTX> TypecheckedBatchValuesIteratorFromBatchValuesIterator<BVI, CTX> {
    pub fn new(bvi: BVI, ctx: CTX) -> Self {
        Self { bvi, ctx }
    }
}

impl<'bvi, 'ctx, BVI, CTX> TypecheckedBatchValuesIterator<'bvi>
    for TypecheckedBatchValuesIteratorFromBatchValuesIterator<BVI, CTX>
where
    BVI: BatchValuesIterator<'bvi>,
    CTX: Iterator<Item = &'ctx RowSerializationContext<'ctx>>,
{
    fn next_serialized(&mut self) -> Option<SerializedResult<'bvi>> {
        if let Some(ctx) = self.ctx.next() {
            let mut data = Vec::new();
            let element_count = {
                let mut writer = RowWriter::new(&mut data);
                if let Some(res) = self.bvi.serialize_next(ctx, &mut writer) {
                    if let Err(e) = res {
                        return Some(Err(e));
                    }
                    match writer.value_count().try_into() {
                        Ok(n) => n,
                        Err(_) => {
                            return Some(Err(SerializationError(Arc::new(
                                SerializeValuesError::TooManyValues,
                            ))))
                        }
                    }
                } else {
                    todo!("Different lengths!");
                }
            };

            Some(Ok(Cow::Owned(SerializedValues {
                serialized_values: data,
                element_count,
            })))
        } else {
            todo!("Maybe Different lengths, return errpr");
        }
    }

    fn write_next_to_request(
        &mut self,
        buf: &mut impl BufMut,
    ) -> Option<Result<(), SerializationError>> {
        let serialized = self.next_serialized()?;
        match serialized {
            Ok(s) => {
                s.as_ref().write_to_request(buf);
                Some(Ok(()))
            }
            Err(e) => Some(Err(e)),
        }
    }

    fn skip_next(&mut self) -> Option<()> {
        todo!()
    }
}

pub struct TypecheckedBatchValuesFromBatchValues<BV, CTX> {
    bv: BV,
    ctx: CTX,
}

impl<'a, BV, CTX> TypecheckedBatchValues for TypecheckedBatchValuesFromBatchValues<BV, CTX>
where
    BV: BatchValues,
    CTX: Iterator<Item = &'a RowSerializationContext<'a>> + Clone,
{
    type TypecheckedBatchValuesIter<'r> = TypecheckedBatchValuesIteratorFromBatchValuesIterator<BV::BatchValuesIter<'r>, CTX>
    where
        Self: 'r;

    fn batch_values_iter(&self) -> Self::TypecheckedBatchValuesIter<'_> {
        TypecheckedBatchValuesIteratorFromBatchValuesIterator::new(
            self.bv.batch_values_iter(),
            self.ctx.clone(),
        )
    }
}
