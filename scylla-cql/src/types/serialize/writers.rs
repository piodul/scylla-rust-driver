//! Contains types and traits used for safe serialization of values for a CQL statement.

use thiserror::Error;

/// Implements a buffer used to serialize data for a query.
///
/// This is a low-level trait. Objects of this type will not be exposed directly
/// to the users, and users should not try to use its methods directly.
pub trait CqlBuffer {
    /// Appends bytes to the end of the buffer.
    fn extend_from_slice(&mut self, bytes: &[u8]);

    /// Returns the current length of the buffer, in bytes.
    fn len(&self) -> usize;

    /// Updates an i32 value at a given position in the buffer.
    ///
    /// May panic if `pos + 4 > self.len()`.
    fn update_i32_at(&mut self, pos: usize, v: i32);
}

impl CqlBuffer for Vec<u8> {
    #[inline]
    fn extend_from_slice(&mut self, bytes: &[u8]) {
        Vec::<u8>::extend_from_slice(self, bytes)
    }

    #[inline]
    fn len(&self) -> usize {
        <[u8]>::len(self)
    }

    #[inline]
    fn update_i32_at(&mut self, pos: usize, v: i32) {
        self[pos..pos + 4].copy_from_slice(&v.to_be_bytes());
    }
}

impl CqlBuffer for usize {
    #[inline]
    fn extend_from_slice(&mut self, bytes: &[u8]) {
        *self += bytes.len();
    }

    #[inline]
    fn len(&self) -> usize {
        *self
    }

    #[inline]
    fn update_i32_at(&mut self, _pos: usize, _v: i32) {
        // Do nothing
    }
}

/// An interface that facilitates writing values for a CQL query.
pub trait RowWriter {
    type CellWriter<'a>: CellWriter
    where
        Self: 'a;

    /// Appends a new value to the sequence and returns an object that allows
    /// to fill it in.
    fn make_cell_writer(&mut self) -> Self::CellWriter<'_>;
}

/// Represents a handle to a CQL value that needs to be written into.
///
/// The writer can either be transformed into a ready value right away
/// (via [`set_null`](CellWriter::set_null),
/// [`set_unset`](CellWriter::set_unset)
/// or [`set_value`](CellWriter::set_value) or transformed into
/// the [`CellWriter::ValueBuilder`] in order to gradually initialize
/// the value when the contents are not available straight away.
///
/// After the value is fully initialized, the handle is consumed and
/// a [`WrittenCellProof`](CellWriter::WrittenCellProof) object is returned
/// in its stead. This is a type-level proof that the value was fully initialized
/// and is used in [`SerializeCql::serialize`](`super::value::SerializeCql::serialize`)
/// in order to enforce the implementor to fully initialize the provided handle
/// to CQL value.
///
/// Dropping this type without calling any of its methods will result
/// in nothing being written.
pub trait CellWriter {
    /// The type of the value builder, returned by the [`CellWriter::into_value_builder`]
    /// method.
    type ValueBuilder: CellValueBuilder<WrittenCellProof = Self::WrittenCellProof>;

    /// An object that serves as a proof that the cell was fully initialized.
    ///
    /// This type is returned by [`set_null`](CellWriter::set_null),
    /// [`set_unset`](CellWriter::set_unset),
    /// [`set_value`](CellWriter::set_value)
    /// and also [`CellValueBuilder::finish`] - generally speaking, after
    /// the value is fully initialized and the `CellWriter` is destroyed.
    ///
    /// The purpose of this type is to enforce the contract of
    /// [`SerializeCql::serialize`](super::value::SerializeCql::serialize): either
    /// the method succeeds and returns a proof that it serialized itself
    /// into the given value, or it fails and returns an error or panics.
    /// The exact type of [`WrittenCellProof`](CellWriter::WrittenCellProof)
    /// is not important as the value is not used at all - it's only
    /// a compile-time check.
    type WrittenCellProof;

    /// Sets this value to be null, consuming this object.
    fn set_null(self) -> Self::WrittenCellProof;

    /// Sets this value to represent an unset value, consuming this object.
    fn set_unset(self) -> Self::WrittenCellProof;

    /// Sets this value to a non-zero, non-unset value with given contents.
    ///
    /// Prefer this to [`into_value_builder`](CellWriter::into_value_builder)
    /// if you have all of the contents of the value ready up front (e.g. for
    /// fixed size types).
    ///
    /// Fails if the contents size overflows the maximum allowed CQL cell size
    /// (which is i32::MAX).
    fn set_value(self, contents: &[u8]) -> Result<Self::WrittenCellProof, CellOverflowError>;

    /// Turns this writter into a [`CellValueBuilder`] which can be used
    /// to gradually initialize the CQL value.
    ///
    /// This method should be used if you don't have all of the data
    /// up front, e.g. when serializing compound types such as collections
    /// or UDTs.
    fn into_value_builder(self) -> Self::ValueBuilder;
}

/// Allows appending bytes to a non-null, non-unset cell.
///
/// This object needs to be dropped in order for the value to be correctly
/// serialized. Failing to drop this value will result in a payload that will
/// not be parsed by the database correctly, but otherwise should not cause
/// data to be misinterpreted.
pub trait CellValueBuilder {
    type SubCellWriter<'a>: CellWriter
    where
        Self: 'a;

    type WrittenCellProof;

    /// Appends raw bytes to this cell.
    fn append_bytes(&mut self, bytes: &[u8]);

    /// Appends a sub-value to the end of the current contents of the cell
    /// and returns an object that allows to fill it in.
    fn make_sub_writer(&mut self) -> Self::SubCellWriter<'_>;

    /// Finishes serializing the value.
    ///
    /// Fails if the constructed cell size overflows the maximum allowed
    /// CQL cell size (which is i32::MAX).
    fn finish(self) -> Result<Self::WrittenCellProof, CellOverflowError>;
}

/// An object that indicates a type-level proof that something was written
/// to a buffer with lifetime `'buf`.
pub struct WrittenCellProof<'buf> {
    /// Using *mut &'buf () is deliberate and makes WrittenCellProof invariant
    /// on the 'buf lifetime parameter.
    /// Ref: https://doc.rust-lang.org/reference/subtyping.html
    _phantom: std::marker::PhantomData<*mut &'buf ()>,
}

impl<'buf> WrittenCellProof<'buf> {
    /// A shorthand for creating the proof.
    ///
    /// Do not make it public! It's important that only the row writer defined
    /// in this module is able to create a proof.
    #[inline]
    fn new() -> Self {
        WrittenCellProof {
            _phantom: std::marker::PhantomData,
        }
    }
}

/// There was an attempt to produce a CQL value over the maximum size limit (i32::MAX)
#[derive(Debug, Clone, Copy, Error)]
#[error("CQL cell overflowed the maximum allowed size of 2^31 - 1")]
pub struct CellOverflowError;

/// A row writer backed by a buffer.
pub struct BufBackedRowWriter<'buf, B> {
    // Buffer that this value should be serialized to.
    buf: &'buf mut B,

    // Number of values written so far.
    value_count: usize,
}

impl<'buf, B> BufBackedRowWriter<'buf, B> {
    /// Creates a new row writer based on an existing Vec.
    ///
    /// The newly created row writer will append data to the end of the vec.
    #[inline]
    pub fn new(buf: &'buf mut B) -> Self {
        Self {
            buf,
            value_count: 0,
        }
    }

    /// Returns the number of values that were written so far.
    ///
    /// Note that the protocol allows at most u16::MAX to be written into a query,
    /// but the writer's interface allows more to be written.
    #[inline]
    pub fn value_count(&self) -> usize {
        self.value_count
    }
}

impl<'buf, B> RowWriter for BufBackedRowWriter<'buf, B>
where
    B: CqlBuffer,
{
    type CellWriter<'a> = BufBackedCellWriter<'a, B> where Self: 'a;

    #[inline]
    fn make_cell_writer(&mut self) -> Self::CellWriter<'_> {
        self.value_count += 1;
        BufBackedCellWriter::new(self.buf)
    }
}

/// A cell writer backed by a buffer.
pub struct BufBackedCellWriter<'buf, B> {
    buf: &'buf mut B,
}

impl<'buf, B> BufBackedCellWriter<'buf, B> {
    /// Creates a new cell writer based on an existing Vec.
    ///
    /// The newly created row writer will append data to the end of the vec.
    #[inline]
    pub fn new(buf: &'buf mut B) -> Self {
        BufBackedCellWriter { buf }
    }
}

impl<'buf, B> CellWriter for BufBackedCellWriter<'buf, B>
where
    B: CqlBuffer,
{
    type ValueBuilder = BufBackedCellValueBuilder<'buf, B>;

    type WrittenCellProof = WrittenCellProof<'buf>;

    #[inline]
    fn set_null(self) -> Self::WrittenCellProof {
        self.buf.extend_from_slice(&(-1i32).to_be_bytes());
        WrittenCellProof::new()
    }

    #[inline]
    fn set_unset(self) -> Self::WrittenCellProof {
        self.buf.extend_from_slice(&(-2i32).to_be_bytes());
        WrittenCellProof::new()
    }

    #[inline]
    fn set_value(self, bytes: &[u8]) -> Result<Self::WrittenCellProof, CellOverflowError> {
        let value_len: i32 = bytes.len().try_into().map_err(|_| CellOverflowError)?;
        self.buf.extend_from_slice(&value_len.to_be_bytes());
        self.buf.extend_from_slice(bytes);
        Ok(WrittenCellProof::new())
    }

    #[inline]
    fn into_value_builder(self) -> Self::ValueBuilder {
        BufBackedCellValueBuilder::new(self.buf)
    }
}

/// A cell value builder backed by a buffer.
pub struct BufBackedCellValueBuilder<'buf, B> {
    // Buffer that this value should be serialized to.
    buf: &'buf mut B,

    // Starting position of the value in the buffer.
    starting_pos: usize,
}

impl<'buf, B> BufBackedCellValueBuilder<'buf, B>
where
    B: CqlBuffer,
{
    #[inline]
    fn new(buf: &'buf mut B) -> Self {
        // "Length" of a [bytes] frame can either be a non-negative i32,
        // -1 (null) or -1 (not set). Push an invalid value here. It will be
        // overwritten eventually either by set_null, set_unset or Drop.
        // If the CellSerializer is not dropped as it should, this will trigger
        // an error on the DB side and the serialized data
        // won't be misinterpreted.
        let starting_pos = buf.len();
        buf.extend_from_slice(&(-3i32).to_be_bytes());
        BufBackedCellValueBuilder { buf, starting_pos }
    }
}

impl<'buf, B> CellValueBuilder for BufBackedCellValueBuilder<'buf, B>
where
    B: CqlBuffer,
{
    type SubCellWriter<'a> = BufBackedCellWriter<'a, B>
    where
        Self: 'a;

    type WrittenCellProof = WrittenCellProof<'buf>;

    #[inline]
    fn append_bytes(&mut self, bytes: &[u8]) {
        self.buf.extend_from_slice(bytes);
    }

    #[inline]
    fn make_sub_writer(&mut self) -> Self::SubCellWriter<'_> {
        BufBackedCellWriter::new(self.buf)
    }

    #[inline]
    fn finish(self) -> Result<Self::WrittenCellProof, CellOverflowError> {
        let value_len: i32 = (self.buf.len() - self.starting_pos - 4)
            .try_into()
            .map_err(|_| CellOverflowError)?;
        self.buf.update_i32_at(self.starting_pos, value_len);
        Ok(WrittenCellProof::new())
    }
}

/// A row writer that does not actually write anything, just counts the bytes.
pub type CountingRowWriter<'buf> = BufBackedRowWriter<'buf, usize>;

/// A cell writer that does not actually write anything, just counts the bytes.
pub type CountingCellWriter<'buf> = BufBackedCellWriter<'buf, usize>;

/// A cell value builder that does not actually write anything, just counts the bytes.
pub type CountingCellValueBuilder<'buf> = BufBackedCellValueBuilder<'buf, usize>;

#[cfg(test)]
mod tests {
    use crate::types::serialize::writers::CountingRowWriter;

    use super::{
        BufBackedCellWriter, BufBackedRowWriter, CellValueBuilder, CellWriter, CountingCellWriter,
        RowWriter,
    };

    // We want to perform the same computation for both buf backed writer
    // and counting writer, but Rust does not support generic closures.
    // This trait comes to the rescue.
    trait CellSerializeCheck {
        fn check<W: CellWriter>(&self, writer: W);
    }

    fn check_cell_serialize<C: CellSerializeCheck>(c: C) -> Vec<u8> {
        let mut data = Vec::new();
        let writer = BufBackedCellWriter::new(&mut data);
        c.check(writer);

        let mut byte_count = 0usize;
        let counting_writer = CountingCellWriter::new(&mut byte_count);
        c.check(counting_writer);

        assert_eq!(data.len(), byte_count);
        data
    }

    #[test]
    fn test_cell_writer() {
        struct Check;
        impl CellSerializeCheck for Check {
            fn check<W: CellWriter>(&self, writer: W) {
                let mut sub_writer = writer.into_value_builder();
                sub_writer.make_sub_writer().set_null();
                sub_writer
                    .make_sub_writer()
                    .set_value(&[1, 2, 3, 4])
                    .unwrap();
                sub_writer.make_sub_writer().set_unset();
                sub_writer.finish().unwrap();
            }
        }

        let data = check_cell_serialize(Check);
        assert_eq!(
            data,
            [
                0, 0, 0, 16, // Length of inner data is 16
                255, 255, 255, 255, // Null (encoded as -1)
                0, 0, 0, 4, 1, 2, 3, 4, // Four byte value
                255, 255, 255, 254, // Unset (encoded as -2)
            ]
        );
    }

    #[test]
    fn test_poisoned_appender() {
        struct Check;
        impl CellSerializeCheck for Check {
            fn check<W: CellWriter>(&self, writer: W) {
                let _ = writer.into_value_builder();
            }
        }

        let data = check_cell_serialize(Check);
        assert_eq!(
            data,
            [
                255, 255, 255, 253, // Invalid value
            ]
        );
    }

    trait RowSerializeCheck {
        fn check<W: RowWriter>(&self, writer: &mut W);
    }

    fn check_row_serialize<C: RowSerializeCheck>(c: C) -> Vec<u8> {
        let mut data = Vec::new();
        let mut writer = BufBackedRowWriter::new(&mut data);
        c.check(&mut writer);

        let mut byte_count = 0usize;
        let mut counting_writer = CountingRowWriter::new(&mut byte_count);
        c.check(&mut counting_writer);

        assert_eq!(data.len(), byte_count);
        data
    }

    #[test]
    fn test_row_writer() {
        struct Check;
        impl RowSerializeCheck for Check {
            fn check<W: RowWriter>(&self, writer: &mut W) {
                writer.make_cell_writer().set_null();
                writer.make_cell_writer().set_value(&[1, 2, 3, 4]).unwrap();
                writer.make_cell_writer().set_unset();
            }
        }

        let data = check_row_serialize(Check);
        assert_eq!(
            data,
            [
                255, 255, 255, 255, // Null (encoded as -1)
                0, 0, 0, 4, 1, 2, 3, 4, // Four byte value
                255, 255, 255, 254, // Unset (encoded as -2)
            ]
        )
    }
}
