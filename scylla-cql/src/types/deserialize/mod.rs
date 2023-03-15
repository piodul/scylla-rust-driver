pub mod row;
pub mod value;

use std::ops::Deref;

use bytes::Bytes;

use crate::frame::frame_errors::ParseError;
use crate::frame::types;

/// A reference to a part of the frame.
#[derive(Clone, Copy, Debug)]
pub struct FrameSlice<'frame> {
    mem: &'frame [u8],
    frame: &'frame Bytes,
}

static EMPTY_BYTES: Bytes = Bytes::new();

impl<'frame> FrameSlice<'frame> {
    /// Creates a new FrameSlice from a reference of a Bytes object.
    ///
    /// This method is exposed to allow writing deserialization tests
    /// for custom
    #[inline]
    pub fn new(frame: &'frame Bytes) -> Self {
        Self { mem: &frame, frame }
    }

    /// Creates a new FrameSlice that refers to a subslice of a given Bytes object.
    #[inline]
    pub fn new_subslice(mem: &'frame [u8], frame: &'frame Bytes) -> Self {
        Self { mem, frame }
    }

    /// Creates an empty FrameSlice.
    #[inline]
    pub fn new_empty() -> Self {
        Self {
            mem: &EMPTY_BYTES,
            frame: &EMPTY_BYTES,
        }
    }

    /// Returns a reference to the slice.
    #[inline]
    pub fn as_slice(&self) -> &'frame [u8] {
        self.mem
    }

    /// Returns a reference to the Bytes object which encompasses the slice.
    ///
    /// The Bytes object will usually be larger than the slice returned by
    /// [FrameSlice::as_slice]. If you wish to obtain a new Bytes object that
    /// points only to the subslice represented by the FrameSlice object,
    /// see [FrameSlice::to_bytes].
    #[inline]
    pub fn as_bytes_ref(&self) -> &'frame Bytes {
        self.frame
    }

    /// Returns a new Bytes object which is a subslice of the original slice
    /// object.
    #[inline]
    pub fn to_bytes(&self) -> Bytes {
        self.frame.slice_ref(self.mem)
    }

    /// Reads and consumes a `[bytes]` item from the beginning of the frame.
    ///
    /// If the operation fails then the slice remains unchanged.
    #[inline]
    fn read_cql_bytes(&mut self) -> Result<Option<FrameSlice<'frame>>, ParseError> {
        match types::read_bytes_opt(&mut self.mem) {
            Ok(Some(slice)) => Ok(Some(Self::new_subslice(slice, self.frame))),
            Ok(None) => Ok(None),
            Err(err) => Err(err),
        }
    }
}

// TODO: Consider whether it is a good idea
impl<'b> Deref for FrameSlice<'b> {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        self.mem
    }
}

// TODO: Hide the iterators inside value.rs
/// Iterates over a sequence of `[bytes]` items from a frame subslice.
///
/// The `[bytes]` items are parsed until the end of subslice is reached.
#[derive(Clone, Copy, Debug)]
pub struct BytesSequenceIterator<'frame> {
    slice: FrameSlice<'frame>,
}

impl<'frame> BytesSequenceIterator<'frame> {
    #[inline]
    fn new(slice: FrameSlice<'frame>) -> Self {
        Self { slice }
    }
}

impl<'frame> From<FrameSlice<'frame>> for BytesSequenceIterator<'frame> {
    #[inline]
    fn from(slice: FrameSlice<'frame>) -> Self {
        Self::new(slice)
    }
}

impl<'frame> Iterator for BytesSequenceIterator<'frame> {
    type Item = Result<Option<FrameSlice<'frame>>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.slice.is_empty() {
            None
        } else {
            Some(self.slice.read_cql_bytes())
        }
    }
}

/// Iterates over a sequence of `[bytes]` items from a frame subslice, expecting
/// a particular number of items.
///
/// The iterator does not consider it to be an error if there are some bytes
/// remaining in the slice after parsing requested amount of items.
#[derive(Clone, Copy, Debug)]
pub struct FixedLengthBytesSequenceIterator<'frame> {
    slice: FrameSlice<'frame>,
    remaining: usize,
}

impl<'frame> FixedLengthBytesSequenceIterator<'frame> {
    pub fn new(count: usize, slice: FrameSlice<'frame>) -> Self {
        Self {
            slice,
            remaining: count,
        }
    }
}

impl<'frame> Iterator for FixedLengthBytesSequenceIterator<'frame> {
    type Item = Result<Option<FrameSlice<'frame>>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.remaining = self.remaining.checked_sub(1)?;
        Some(self.slice.read_cql_bytes())
    }
}

#[cfg(test)]
mod tests {
    use crate::frame::types;

    use super::*;

    use bytes::{Bytes, BytesMut};

    static CELL1: &'static [u8] = &[1, 2, 3];
    static CELL2: &'static [u8] = &[4, 5, 6, 7];

    pub(super) fn serialize_cells(
        cells: impl IntoIterator<Item = Option<impl AsRef<[u8]>>>,
    ) -> Bytes {
        let mut bytes = BytesMut::new();
        for cell in cells {
            types::write_bytes_opt(cell, &mut bytes).unwrap();
        }
        bytes.freeze()
    }

    #[test]
    fn test_cql_bytes_consumption() {
        let frame = serialize_cells([Some(CELL1), None, Some(CELL2)]);
        let mut slice = FrameSlice::new(&frame);
        assert!(!slice.is_empty());

        assert_eq!(slice.read_cql_bytes().unwrap().as_deref(), Some(CELL1));
        assert!(!slice.is_empty());
        assert_eq!(slice.read_cql_bytes().unwrap().as_deref(), None);
        assert!(!slice.is_empty());
        assert_eq!(slice.read_cql_bytes().unwrap().as_deref(), Some(CELL2));
        assert!(slice.is_empty());
        slice.read_cql_bytes().unwrap_err();
        assert!(slice.is_empty());
    }

    #[test]
    fn test_cql_bytes_owned() {
        let frame = serialize_cells([Some(CELL1), Some(CELL2)]);
        let mut slice = FrameSlice::new(&frame);

        let subslice1 = slice.read_cql_bytes().unwrap().unwrap();
        let subslice2 = slice.read_cql_bytes().unwrap().unwrap();

        assert_eq!(subslice1.as_slice(), CELL1);
        assert_eq!(subslice2.as_slice(), CELL2);

        assert_eq!(
            subslice1.as_bytes_ref() as *const Bytes,
            &frame as *const Bytes
        );
        assert_eq!(
            subslice2.as_bytes_ref() as *const Bytes,
            &frame as *const Bytes
        );

        let subslice1_bytes = subslice1.to_bytes();
        let subslice2_bytes = subslice2.to_bytes();

        assert_eq!(subslice1.as_slice(), subslice1_bytes.as_ref());
        assert_eq!(subslice2.as_slice(), subslice2_bytes.as_ref());
    }
}
