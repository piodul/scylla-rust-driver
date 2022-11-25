use bytes::Bytes;

use crate::frame::frame_errors::ParseError;
use crate::frame::response::result::{ColumnSpec, ColumnType};
use crate::frame::types;

/// Iterates over the whole Rows result.
#[derive(Clone, Debug)]
pub struct RowsIterator<'rows> {
    mem: &'rows [u8],
    col_specs: &'rows [ColumnSpec],
    rows_remaining: usize,

    // A reference to the original bytes::Bytes object. We need this
    // in order to be able to return owned sub-slices of the original
    // Bytes object via Bytes::slice_ref.
    //
    // TODO: Bytes::slice_ref does some unnecessary bound checks which could
    // be elided. There could be a "Ref" object which points to the same
    // piece of memory as some existing Bytes object, could be cheaply
    // sub-sliced, and could return an owned slice object relatively cheaply.
    //
    // However:
    // - This is not possible without modifications to the `bytes` library
    // - I have no proof that it would significantly speed up deserialization
    //
    // Maybe if this is fixed then we could attempt the thing described above:
    // https://github.com/tokio-rs/bytes/issues/300
    original_bytes: &'rows Bytes,
}

impl<'rows> RowsIterator<'rows> {
    pub(crate) fn new(
        mem: &'rows [u8],
        col_specs: &'rows [ColumnSpec],
        rows_count: usize,
        original_bytes: &'rows Bytes,
    ) -> Self {
        Self {
            mem: &mem,
            col_specs,
            rows_remaining: rows_count,
            original_bytes,
        }
    }
}

impl<'rows> Iterator for RowsIterator<'rows> {
    type Item = Result<ValueIterator<'rows>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.rows_remaining = self.rows_remaining.checked_sub(1)?;

        // Need to manually iterate over the values
        // Hopefully this is cheap to do twice (once here, the second time
        // by the iterator)
        let old_mem = self.mem;
        for _ in 0..self.col_specs.len() {
            if let Err(err) = types::read_bytes_opt(&mut self.mem) {
                return Some(Err(err));
            }
        }

        Some(Ok(ValueIterator {
            mem: old_mem,
            col_specs: self.col_specs,
            original_bytes: self.original_bytes,
        }))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.rows_remaining, Some(self.rows_remaining))
    }
}

/// Iterates over values.
#[derive(Clone, Debug)]
pub struct ValueIterator<'rows> {
    mem: &'rows [u8],
    col_specs: &'rows [ColumnSpec],

    original_bytes: &'rows Bytes,
}

impl<'rows> Iterator for ValueIterator<'rows> {
    type Item = Result<RawValue<'rows>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        let (head, tail) = self.col_specs.split_first()?;

        types::read_bytes_opt(&mut self.mem)
            .map(|value| {
                self.col_specs = tail;
                Some(RawValue {
                    typ: &head.typ,
                    value,
                    original_bytes: self.original_bytes,
                })
            })
            .transpose()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.col_specs.len();
        (remaining, Some(remaining))
    }
}

pub struct RawValue<'rows> {
    typ: &'rows ColumnType,
    value: Option<&'rows [u8]>,
    original_bytes: &'rows Bytes,
}

impl<'rows> RawValue<'rows> {
    pub fn typ(&self) -> &'rows ColumnType {
        self.typ
    }

    pub fn value(&self) -> Option<&'rows [u8]> {
        self.value
    }

    pub fn value_owned(&self) -> Option<bytes::Bytes> {
        self.value.map(|v| self.original_bytes.slice_ref(v))
    }
}

// TODO: Tests?
