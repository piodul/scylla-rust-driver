use super::row::SerializeRow;

/// Represents List of SerializeRow for Batch statement
pub trait BatchValues {
    /// Returns an iterator over
    // For some unknown reason, this type, when not resolved to a concrete type for a given async function,
    // cannot live across await boundaries while maintaining the corresponding future `Send`, unless `'r: 'static`
    //
    // See <https://github.com/scylladb/scylla-rust-driver/issues/599> for more details
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
pub trait BatchValuesIterator<'bv> {
    type Row<'r>: SerializeRow
    where
        Self: 'r;

    /// Return values for the next statement in the batch.
    fn next(&mut self) -> Option<Self::Row<'_>>;

    /// Skips the next set of values.
    fn skip_next(&mut self) -> Option<()>;

    /// Return the number of sets of values, consuming the iterator in the process.
    #[inline]
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

impl<'bv, 'sr: 'bv, IT, SR> BatchValuesIterator<'bv> for BatchValuesIteratorFromIterator<IT>
where
    IT: Iterator<Item = &'sr SR>,
    SR: SerializeRow + 'sr,
{
    type Row<'r> = &'sr SR where Self: 'r;

    #[inline]
    fn next(&mut self) -> Option<Self::Row<'_>> {
        self.it.next()
    }

    #[inline]
    fn skip_next(&mut self) -> Option<()> {
        self.it.next().map(|_| ())
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.it.count()
    }
}

impl<IT> From<IT> for BatchValuesIteratorFromIterator<IT>
where
    IT: Iterator,
    IT::Item: SerializeRow,
{
    #[inline]
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
pub struct BatchValuesFromIterator<'sr, IT> {
    it: IT,

    // Why is this needed??? Without it impl BatchValues for BatchValuesFromIter doesn't work
    _phantom: std::marker::PhantomData<&'sr ()>,
}

impl<'sr, IT, SR> BatchValuesFromIterator<'sr, IT>
where
    IT: Iterator<Item = &'sr SR> + Clone,
    SR: SerializeRow + 'sr,
{
    #[inline]
    pub fn new(into_iter: impl IntoIterator<IntoIter = IT>) -> Self {
        Self {
            it: into_iter.into_iter(),
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<'sr, IT, SR> From<IT> for BatchValuesFromIterator<'sr, IT>
where
    IT: Iterator<Item = &'sr SR> + Clone,
    SR: SerializeRow + 'sr,
{
    #[inline]
    fn from(it: IT) -> Self {
        Self::new(it)
    }
}

impl<'sr, IT, SR> BatchValues for BatchValuesFromIterator<'sr, IT>
where
    IT: Iterator<Item = &'sr SR> + Clone,
    SR: SerializeRow + 'sr,
{
    type BatchValuesIter<'r> = BatchValuesIteratorFromIterator<IT> where Self: 'r;

    #[inline]
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        self.it.clone().into()
    }
}

// Implement BatchValues for slices of SerializeRow types
impl<T: SerializeRow> BatchValues for [T] {
    type BatchValuesIter<'r> = BatchValuesIteratorFromIterator<std::slice::Iter<'r, T>> where Self: 'r;

    #[inline]
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        self.iter().into()
    }
}

// Implement BatchValues for Vec<SerializeRow>
impl<T: SerializeRow> BatchValues for Vec<T> {
    type BatchValuesIter<'r> = BatchValuesIteratorFromIterator<std::slice::Iter<'r, T>> where Self: 'r;

    #[inline]
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        BatchValues::batch_values_iter(self.as_slice())
    }
}

// Here is an example implementation for (T0, )
// Further variants are done using a macro
impl<T0: SerializeRow> BatchValues for (T0,) {
    type BatchValuesIter<'r> = BatchValuesIteratorFromIterator<std::iter::Once<&'r T0>> where Self: 'r;

    #[inline]
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        std::iter::once(&self.0).into()
    }
}

pub struct TupleValuesIter<'sr, T> {
    tuple: &'sr T,
    idx: usize,
}

macro_rules! impl_batch_values_for_tuple {
    ( $($Ti:ident),* ; $($FieldI:tt),* ; $TupleSize:tt) => {
        impl<$($Ti),+> BatchValues for ($($Ti,)+)
        where
            $($Ti: SerializeRow),+
        {
            type BatchValuesIter<'r> = TupleValuesIter<'r, ($($Ti,)+)> where Self: 'r;

            #[inline]
            fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
                TupleValuesIter {
                    tuple: self,
                    idx: 0,
                }
            }
        }

        impl<'bv, $($Ti),+> BatchValuesIterator<'bv> for TupleValuesIter<'bv, ($($Ti,)+)>
        where
            $($Ti: SerializeRow),+
        {
            type Row<'q> = &'q dyn SerializeRow where Self: 'q;

            fn next(&mut self) -> Option<Self::Row<'_>> {
                let ret = match self.idx {
                    $(
                        $FieldI => &self.tuple.$FieldI as &dyn SerializeRow,
                    )*
                    _ => return None,
                };
                self.idx += 1;
                Some(ret)
            }

            #[inline]
            fn skip_next(&mut self) -> Option<()> {
                if self.idx < $TupleSize {
                    self.idx += 1;
                    Some(())
                } else {
                    None
                }
            }

            #[inline]
            fn count(self) -> usize {
                $TupleSize - self.idx
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

    #[inline]
    fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
        <T as BatchValues>::batch_values_iter(*self)
    }
}

// The "first serialized" optimization

pub mod first_serialized {
    // TODO: Should this module be in `scylla` and be hidden?
    use crate::_macro_internal::{RowWriter, SerializationError, SerializeRow};
    use crate::frame::types::RawValue;
    use crate::types::serialize::row::SerializedValues;

    use super::{BatchValues, BatchValuesIterator};

    pub struct BatchValuesFirstSerialized<'f, BV> {
        // Contains the first value of BV in a serialized form.
        // The first value in the iterator returned from `rest` should be skipped!
        first: Option<&'f SerializedValues>,
        rest: BV,
    }

    impl<'f, BV> BatchValuesFirstSerialized<'f, BV> {
        #[inline]
        pub fn new(rest: BV, first: Option<&'f SerializedValues>) -> Self {
            Self { first, rest }
        }
    }

    impl<'f, BV> BatchValues for BatchValuesFirstSerialized<'f, BV>
    where
        BV: BatchValues,
    {
        type BatchValuesIter<'r> = BatchValuesFirstSerializedIterator<'r, BV::BatchValuesIter<'r>>
    where
        Self: 'r;

        fn batch_values_iter(&self) -> Self::BatchValuesIter<'_> {
            BatchValuesFirstSerializedIterator {
                first: self.first.clone(),
                rest: self.rest.batch_values_iter(),
            }
        }
    }

    pub struct BatchValuesFirstSerializedIterator<'f, BVI> {
        first: Option<&'f SerializedValues>,
        rest: BVI,
    }

    impl<'f, BVI> BatchValuesIterator<'f> for BatchValuesFirstSerializedIterator<'f, BVI>
    where
        BVI: BatchValuesIterator<'f>,
    {
        type Row<'r> = BatchValuesFirstSerializedRow<'r, BVI::Row<'r>>
    where
        Self: 'r;

        #[inline]
        fn next(&mut self) -> Option<Self::Row<'_>> {
            match self.first.take() {
                Some(s) => {
                    self.rest.skip_next();
                    Some(BatchValuesFirstSerializedRow::Serialized(s))
                }
                None => self
                    .rest
                    .next()
                    .map(BatchValuesFirstSerializedRow::Unserialized),
            }
        }

        #[inline]
        fn skip_next(&mut self) -> Option<()> {
            self.first = None;
            self.rest.skip_next()
        }

        #[inline]
        fn count(self) -> usize
        where
            Self: Sized,
        {
            self.rest.count()
        }
    }

    pub enum BatchValuesFirstSerializedRow<'f, R> {
        Serialized(&'f SerializedValues),
        Unserialized(R),
    }

    impl<'f, R> SerializeRow for BatchValuesFirstSerializedRow<'f, R>
    where
        R: SerializeRow,
    {
        #[inline]
        fn serialize(
            &self,
            ctx: &crate::_macro_internal::RowSerializationContext<'_>,
            writer: &mut RowWriter,
        ) -> Result<(), SerializationError> {
            match self {
                BatchValuesFirstSerializedRow::Serialized(s) => {
                    // TODO: We should just be able to copy the bytes
                    for v in s.iter() {
                        let writer = writer.make_cell_writer();
                        match v {
                            RawValue::Null => writer.set_null(),
                            RawValue::Unset => writer.set_unset(),
                            RawValue::Value(v) => {
                                writer.set_value(v).map_err(SerializationError::new)?
                            }
                        };
                    }
                    Ok(())
                }
                BatchValuesFirstSerializedRow::Unserialized(u) => u.serialize(ctx, writer),
            }
        }

        #[inline]
        fn is_empty(&self) -> bool {
            match self {
                BatchValuesFirstSerializedRow::Serialized(s) => s.is_empty(),
                BatchValuesFirstSerializedRow::Unserialized(u) => u.is_empty(),
            }
        }
    }
}
