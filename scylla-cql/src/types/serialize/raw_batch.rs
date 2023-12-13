use crate::frame::types::RawValue;

use super::row::SerializedValues;
use super::{RowWriter, SerializationError};

/// A version of `scylla`'s `BatchValues` which knows how to serialize itself
/// without the need to supply serialization context from the outside.
pub trait RawBatchValues {
    // For some unknown reason, this type, when not resolved to a concrete type for a given async function,
    // cannot live across await boundaries while maintaining the corresponding future `Send`, unless `'r: 'static`
    //
    // See <https://github.com/scylladb/scylla-rust-driver/issues/599> for more details
    type RawBatchValuesIter<'r>: RawBatchValuesIterator<'r>
    where
        Self: 'r;

    fn batch_values_iter(&self) -> Self::RawBatchValuesIter<'_>;
}

/// An iterator-like for `ValueList`
///
/// An instance of this can be easily obtained from `IT: Iterator<Item: ValueList>`: that would be
/// `BatchValuesIteratorFromIterator<IT>`
///
/// It's just essentially making methods from `ValueList` accessible instead of being an actual iterator because of
/// compiler limitations that would otherwise be very complex to overcome.
/// (specifically, types being different would require yielding enums for tuple impls)
pub trait RawBatchValuesIterator<'a> {
    type Row<'r>: RawSerializeRow
    where
        Self: 'r;

    fn next(&mut self) -> Option<Self::Row<'_>>;

    fn skip_next(&mut self) -> Option<()>;

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

/// A proxy for a `SerializeValue` which knows how to serialize itself into
/// an untyped representation, or already is serialized in an untyped form.
pub trait RawSerializeRow {
    fn serialize(&self, writer: &mut RowWriter<'_>) -> Result<(), SerializationError>;
}

/// An implementation used by `scylla-proxy`
impl RawBatchValues for Vec<SerializedValues> {
    type RawBatchValuesIter<'r> = std::slice::Iter<'r, SerializedValues>
    where
        Self: 'r;

    fn batch_values_iter(&self) -> Self::RawBatchValuesIter<'_> {
        self.iter()
    }
}

impl<'r> RawBatchValuesIterator<'r> for std::slice::Iter<'r, SerializedValues> {
    type Row<'q> = &'r SerializedValues
    where
        Self: 'q;

    #[inline]
    fn next(&mut self) -> Option<Self::Row<'_>> {
        <_ as Iterator>::next(self)
    }

    #[inline]
    fn skip_next(&mut self) -> Option<()> {
        <_ as Iterator>::next(self).map(|_| ())
    }

    #[inline]
    fn count(self) -> usize {
        <_ as Iterator>::count(self)
    }
}

impl<'r> RawSerializeRow for &'r SerializedValues {
    #[inline]
    fn serialize(&self, writer: &mut RowWriter<'_>) -> Result<(), SerializationError> {
        for v in self.iter() {
            let writer = writer.make_cell_writer();
            match v {
                RawValue::Null => writer.set_null(),
                RawValue::Unset => writer.set_unset(),
                RawValue::Value(v) => writer.set_value(v).map_err(SerializationError::new)?,
            };
        }
        Ok(())
    }
}
