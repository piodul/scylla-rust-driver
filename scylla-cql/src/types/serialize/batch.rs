use super::row::RowSerializationContext;
use super::row::SerializeRow;
use super::writers::RowWriter;
use super::SerializationError;

/// Represents List of SerializeRow for Batch statement
pub trait BatchValues {
    /// For some unknown reason, this type, when not resolved to a concrete type for a given async function,
    /// cannot live across await boundaries while maintaining the corresponding future `Send`, unless `'r: 'static`
    ///
    /// See <https://github.com/scylladb/scylla-rust-driver/issues/599> for more details
    type BatchValuesIter<'r>: BatchValuesIterator<'r>
    where
        Self: 'r;
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_>;
}

/// An iterator-like for `SerializeRow`
///
/// An instance of this can be easily obtained from `IT: Iterator<Item: SerializeRow>`: that would be
/// `BatchValuesIteratorFromIterator<IT>`
///
/// It's just essentially making methods from `SerializeRow` accessible instead of being an actual iterator because of
/// compiler limitations that would otherwise be very complex to overcome.
/// (specifically, types being different would require yielding enums for tuple impls)
pub trait BatchValuesIterator<'a> {
    fn serialize_next(
        &mut self,
        ctx: &RowSerializationContext,
        writer: &mut RowWriter,
    ) -> Option<Result<(), SerializationError>>;
    fn is_next_empty(&mut self) -> Option<bool>;
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
pub struct BatchValuesIteratorFromIterator<IT: Iterator> {
    it: IT,
}

impl<'r, 'a: 'r, IT, VL> BatchValuesIterator<'r> for BatchValuesIteratorFromIterator<IT>
where
    IT: Iterator<Item = &'a VL>,
    VL: SerializeRow + 'a,
{
    fn serialize_next(
        &mut self,
        ctx: &RowSerializationContext,
        writer: &mut RowWriter,
    ) -> Option<Result<(), SerializationError>> {
        self.it.next().map(|vl| vl.serialize(ctx, writer))
    }
    fn is_next_empty(&mut self) -> Option<bool> {
        self.it.next().map(|sr| sr.is_empty())
    }
    fn skip_next(&mut self) -> Option<()> {
        self.it.next().map(|_| ())
    }
}

impl<IT> From<IT> for BatchValuesIteratorFromIterator<IT>
where
    IT: Iterator,
    IT::Item: SerializeRow,
{
    fn from(it: IT) -> Self {
        BatchValuesIteratorFromIterator { it }
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
pub struct BatchValuesFromIter<'a, IT> {
    it: IT,
    _spooky: std::marker::PhantomData<&'a ()>,
}

impl<'a, IT, VL> BatchValuesFromIter<'a, IT>
where
    IT: Iterator<Item = &'a VL> + Clone,
    VL: SerializeRow + 'a,
{
    pub fn new(into_iter: impl IntoIterator<IntoIter = IT>) -> Self {
        Self {
            it: into_iter.into_iter(),
            _spooky: std::marker::PhantomData,
        }
    }
}

impl<'a, IT, VL> From<IT> for BatchValuesFromIter<'a, IT>
where
    IT: Iterator<Item = &'a VL> + Clone,
    VL: SerializeRow + 'a,
{
    fn from(it: IT) -> Self {
        Self::new(it)
    }
}

impl<'a, IT, VL> BatchValues for BatchValuesFromIter<'a, IT>
where
    IT: Iterator<Item = &'a VL> + Clone,
    VL: SerializeRow + 'a,
{
    type BatchValuesIter<'r> = BatchValuesIteratorFromIterator<IT> where Self: 'r;
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        self.it.clone().into()
    }
}

// Implement BatchValues for slices of SerializeRow types
impl<T: SerializeRow> BatchValues for [T] {
    type BatchValuesIter<'r> = BatchValuesIteratorFromIterator<std::slice::Iter<'r, T>> where Self: 'r;
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        self.iter().into()
    }
}

// Implement BatchValues for Vec<SerializeRow>
impl<T: SerializeRow> BatchValues for Vec<T> {
    type BatchValuesIter<'r> = BatchValuesIteratorFromIterator<std::slice::Iter<'r, T>> where Self: 'r;
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        BatchValues::batch_values_iter(self.as_slice())
    }
}

// Here is an example implementation for (T0, )
// Further variants are done using a macro
impl<T0: SerializeRow> BatchValues for (T0,) {
    type BatchValuesIter<'r> = BatchValuesIteratorFromIterator<std::iter::Once<&'r T0>> where Self: 'r;
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        std::iter::once(&self.0).into()
    }
}

pub struct TupleValuesIter<'a, T> {
    tuple: &'a T,
    idx: usize,
}

macro_rules! impl_batch_values_for_tuple {
    ( $($Ti:ident),* ; $($FieldI:tt),* ; $TupleSize:tt) => {
        impl<$($Ti),+> BatchValues for ($($Ti,)+)
        where
            $($Ti: SerializeRow),+
        {
            type BatchValuesIter<'r> = TupleValuesIter<'r, ($($Ti,)+)> where Self: 'r;
            fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
                TupleValuesIter {
                    tuple: self,
                    idx: 0,
                }
            }
        }
        impl<'r, $($Ti),+> BatchValuesIterator<'r> for TupleValuesIter<'r, ($($Ti,)+)>
        where
            $($Ti: SerializeRow),+
        {
            fn serialize_next(
                &mut self,
                ctx: &RowSerializationContext,
                writer: &mut RowWriter,
            ) -> Option<Result<(), SerializationError>> {
                let ret = match self.idx {
                    $(
                        $FieldI => self.tuple.$FieldI.serialize(ctx, writer),
                    )*
                    _ => return None,
                };
                self.idx += 1;
                Some(ret)
            }
            fn is_next_empty(&mut self) -> Option<bool> {
                let ret = match self.idx {
                    $(
                        $FieldI => self.tuple.$FieldI.is_empty(),
                    )*
                    _ => return None,
                };
                self.idx += 1;
                Some(ret)
            }
            fn skip_next(&mut self) -> Option<()> {
                if self.idx < $TupleSize {
                    self.idx += 1;
                    Some(())
                } else {
                    None
                }
            }
        }
    }
}

impl_batch_values_for_tuple!(T0, T1; 0, 1; 2);
impl_batch_values_for_tuple!(T0, T1, T2; 0, 1, 2; 3);
impl_batch_values_for_tuple!(T0, T1, T2, T3; 0, 1, 2, 3; 4);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4; 0, 1, 2, 3, 4; 5);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5; 0, 1, 2, 3, 4, 5; 6);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6; 0, 1, 2, 3, 4, 5, 6; 7);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7; 0, 1, 2, 3, 4, 5, 6, 7; 8);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8; 0, 1, 2, 3, 4, 5, 6, 7, 8; 9);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9;
                             0, 1, 2, 3, 4, 5, 6, 7, 8, 9; 10);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10;
                             0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10; 11);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11;
                             0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11; 12);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12;
                             0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12; 13);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13;
                             0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13; 14);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14;
                             0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14; 15);
impl_batch_values_for_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15;
                             0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15; 16);

// Every &impl BatchValues should also implement BatchValues
impl<'a, T: BatchValues + ?Sized> BatchValues for &'a T {
    type BatchValuesIter<'r> = <T as BatchValues>::BatchValuesIter<'r> where Self: 'r;
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        <T as BatchValues>::batch_values_iter(*self)
    }
}
