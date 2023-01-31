//! Provides types for dealing with row deserialization.

use std::marker::PhantomData;

use super::value::DeserializeCql;
use super::FrameSlice;
use crate::frame::frame_errors::ParseError;
use crate::frame::response::result::CqlValue;
use crate::frame::response::result::{ColumnSpec, Row};

/// Represents a raw, unparsed column value.
#[non_exhaustive]
pub struct RawColumn<'frame> {
    pub spec: &'frame ColumnSpec,
    pub slice: Option<FrameSlice<'frame>>,
}

/// Iterates over columns of a single row.
#[derive(Clone, Debug)]
pub struct ColumnIterator<'frame> {
    specs: std::slice::Iter<'frame, ColumnSpec>,
    slice: FrameSlice<'frame>,
}

impl<'frame> ColumnIterator<'frame> {
    /// Creates a new iterator over a single row.
    ///
    /// - `specs` - information about columns of the serialized response,
    /// - `slice` - a `FrameSlice` which points to the serialized row.
    #[inline]
    pub fn new(specs: &'frame [ColumnSpec], slice: FrameSlice<'frame>) -> Self {
        Self {
            specs: specs.iter(),
            slice,
        }
    }

    /// Returns the remaining number of rows that this iterator is expected
    /// to return.
    #[inline]
    pub fn columns_remaining(&self) -> usize {
        self.specs.len()
    }
}

impl<'frame> Iterator for ColumnIterator<'frame> {
    type Item = Result<RawColumn<'frame>, ParseError>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let spec = self.specs.next()?;
        Some(
            self.slice
                .read_cql_bytes()
                .map(|slice| RawColumn { spec, slice }),
        )
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.specs.len()))
    }
}

/// Iterates over the whole result, returning rows.
pub struct RowIterator<'frame> {
    specs: &'frame [ColumnSpec],
    remaining: usize,
    slice: FrameSlice<'frame>,
}

impl<'frame> RowIterator<'frame> {
    /// Creates a new iterator over rows from a serialized response.
    ///
    /// - `remaining` - number of the remaining rows in the serialized response,
    /// - `specs` - information about columns of the serialized response,
    /// - `slice` - a `FrameSlice` that points to the serialized rows data.
    #[inline]
    pub fn new(remaining: usize, specs: &'frame [ColumnSpec], slice: FrameSlice<'frame>) -> Self {
        Self {
            specs,
            remaining,
            slice,
        }
    }

    /// Returns information about the columns of rows that are iterated over.
    #[inline]
    pub fn specs(&self) -> &'frame [ColumnSpec] {
        self.specs
    }

    /// Returns the remaining number of rows that this iterator is supposed
    /// to return.
    #[inline]
    pub fn rows_remaining(&self) -> usize {
        self.remaining
    }
}

impl<'frame> Iterator for RowIterator<'frame> {
    type Item = Result<ColumnIterator<'frame>, ParseError>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.remaining = self.remaining.checked_sub(1)?;

        let iter = ColumnIterator::new(self.specs, self.slice);

        // Skip the row here, manually
        for _ in 0..self.specs.len() {
            if let Err(err) = self.slice.read_cql_bytes() {
                return Some(Err(err));
            }
        }

        Some(Ok(iter))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

/// A typed version of `RowIterator` which deserializes the rows before
/// returning them.
pub struct TypedRowIterator<'frame, R> {
    inner: RowIterator<'frame>,
    _phantom: PhantomData<R>,
}

impl<'frame, R> TypedRowIterator<'frame, R>
where
    R: DeserializeRow<'frame>,
{
    /// Creates a new `TypedRowIterator` from given `RowIterator`.
    ///
    /// Calls `R::type_check` and fails if the type check fails.
    #[inline]
    pub fn new(raw: RowIterator<'frame>) -> Result<Self, ParseError> {
        R::type_check(raw.specs())?;
        Ok(Self {
            inner: raw,
            _phantom: PhantomData,
        })
    }

    /// Returns information about the columns of rows that are iterated over.
    #[inline]
    pub fn specs(&self) -> &'frame [ColumnSpec] {
        self.inner.specs()
    }

    /// Returns the remaining number of rows that this iterator is supposed
    /// to return.
    #[inline]
    pub fn rows_remaining(&self) -> usize {
        self.inner.rows_remaining()
    }
}

impl<'frame, R> Iterator for TypedRowIterator<'frame, R>
where
    R: DeserializeRow<'frame>,
{
    type Item = Result<R, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw = match self.inner.next() {
            Some(Ok(raw)) => raw,
            Some(Err(err)) => return Some(Err(err)),
            None => return None,
        };

        Some(R::deserialize(raw))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// A type that can be deserialized from a row that was returned from a query.
///
/// For tips on how to write a custom implementation of this trait, see the
/// documentation of the parent module.
///
/// The crate also provides a derive macro which allows to automatically
/// implement the trait for a custom type. For more details on what the macro
/// is capable of, see its documentation.
pub trait DeserializeRow<'frame>
where
    Self: Sized,
{
    /// Checks that the schema of the result matches what this type expects.
    ///
    /// This function can check whether column types and names match the
    /// expectations.
    fn type_check(specs: &[ColumnSpec]) -> Result<(), ParseError>;

    /// Deserializes a row from given column iterator.
    ///
    /// This function can assume that the driver called `type_check` to verify
    /// the row's type. Note that `deserialize` is not an unsafe function,
    /// so it should not use the assumption about `type_check` being called
    /// as an excuse to run `unsafe` code.
    fn deserialize(row: ColumnIterator<'frame>) -> Result<Self, ParseError>;
}

impl<'frame> DeserializeRow<'frame> for Row {
    #[inline]
    fn type_check(_specs: &[ColumnSpec]) -> Result<(), ParseError> {
        // CqlValues accept all types, no type checking needed
        Ok(())
    }

    #[inline]
    fn deserialize(mut row: ColumnIterator<'frame>) -> Result<Self, ParseError> {
        let mut columns = Vec::with_capacity(row.size_hint().0);
        while let Some(column) = row.next().transpose()? {
            columns.push(<Option<CqlValue>>::deserialize(
                &column.spec.typ,
                column.slice,
            )?);
        }
        Ok(Self { columns })
    }
}

impl<'frame> DeserializeRow<'frame> for ColumnIterator<'frame> {
    #[inline]
    fn type_check(_specs: &[ColumnSpec]) -> Result<(), ParseError> {
        Ok(())
    }

    #[inline]
    fn deserialize(row: ColumnIterator<'frame>) -> Result<Self, ParseError> {
        Ok(row)
    }
}

macro_rules! impl_tuple {
    ($($Ti:ident),*; $($idx:literal),*; $($idf:ident),*) => {
        impl<'frame, $($Ti),*> DeserializeRow<'frame> for ($($Ti,)*)
        where
            $($Ti: DeserializeCql<'frame>),*
        {
            fn type_check(specs: &[ColumnSpec]) -> Result<(), ParseError> {
                if let [$($idf),*] = &specs {
                    $(
                        <$Ti as DeserializeCql<'frame>>::type_check(&$idf.typ)?;
                    )*
                    return Ok(());
                }
                const TUPLE_LEN: usize = [0, $($idx),*].len() - 1;
                return Err(ParseError::BadIncomingData(format!(
                    "Expected {} columns, but got {:?}",
                    TUPLE_LEN, specs.len(),
                )));
            }

            fn deserialize(mut row: ColumnIterator<'frame>) -> Result<Self, ParseError> {
                const TUPLE_LEN: usize = [0, $($idx),*].len() - 1;
                let ret = (
                    $({
                        let column = row.next().ok_or_else(|| ParseError::BadIncomingData(
                            format!("Expected {} values, got {}", TUPLE_LEN, $idx)
                        ))??;
                        <$Ti as DeserializeCql<'frame>>::deserialize(&column.spec.typ, column.slice)?
                    },)*
                );
                if row.next().is_some() {
                    return Err(ParseError::BadIncomingData(
                        format!("Expected {} values, but got more", TUPLE_LEN)
                    ));
                }
                Ok(ret)
            }
        }
    }
}

macro_rules! impl_tuple_multiple {
    (;;) => {
        impl_tuple!(;;);
    };
    ($TN:ident $(,$Ti:ident)*; $idx_n:literal $(,$idx:literal)*; $idf_n:ident $(,$idf:ident)*) => {
        impl_tuple_multiple!($($Ti),*; $($idx),*; $($idf),*);
        impl_tuple!($TN $(,$Ti)*; $idx_n $(,$idx)*; $idf_n $(,$idf)*);
    }
}

impl_tuple_multiple!(
    T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15;
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15;
    t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15
);

#[cfg(test)]
mod tests {
    use bytes::Bytes;
    use scylla_macros::DeserializeRow;

    use crate::frame::frame_errors::ParseError;
    use crate::frame::response::result::{ColumnSpec, ColumnType, TableSpec};
    use crate::types::deserialize::FrameSlice;

    use super::super::tests::serialize_cells;
    use super::{ColumnIterator, DeserializeRow};

    #[test]
    fn test_tuple_deserialization() {
        // Empty tuple
        deserialize::<()>(&[], &Bytes::new()).unwrap();

        // 1-elem tuple
        let (a,) = deserialize::<(i32,)>(
            &[spec("i", ColumnType::Int)],
            &serialize_cells([val_int(123)]),
        )
        .unwrap();
        assert_eq!(a, 123);

        // 3-elem tuple
        let (a, b, c) = deserialize::<(i32, i32, i32)>(
            &[
                spec("i1", ColumnType::Int),
                spec("i2", ColumnType::Int),
                spec("i3", ColumnType::Int),
            ],
            &serialize_cells([val_int(123), val_int(456), val_int(789)]),
        )
        .unwrap();
        assert_eq!((a, b, c), (123, 456, 789));

        // Make sure that column type mismatch is detected
        deserialize::<(i32, String, i32)>(
            &[
                spec("i1", ColumnType::Int),
                spec("i2", ColumnType::Int),
                spec("i3", ColumnType::Int),
            ],
            &serialize_cells([val_int(123), val_int(456), val_int(789)]),
        )
        .unwrap_err();

        // Make sure that borrowing types compile and work correctly
        let specs = &[spec("s", ColumnType::Text)];
        let byts = serialize_cells([val_str("abc")]);
        let (s,) = deserialize::<(&str,)>(specs, &byts).unwrap();
        assert_eq!(s, "abc");
    }

    #[test]
    fn test_struct_deserialization_loose_ordering() {
        #[derive(DeserializeRow, PartialEq, Eq, Debug)]
        #[scylla(crate = "crate")]
        struct MyRow<'a> {
            a: &'a str,
            b: Option<i32>,
            #[scylla(skip)]
            c: String,
        }

        // Original order of columns
        let specs = &[spec("a", ColumnType::Text), spec("b", ColumnType::Int)];
        let byts = serialize_cells([val_str("abc"), val_int(123)]);
        let row = deserialize::<MyRow<'_>>(specs, &byts).unwrap();
        assert_eq!(
            row,
            MyRow {
                a: "abc",
                b: Some(123),
                c: String::new(),
            }
        );

        // Different order of columns - should still work
        let specs = &[spec("b", ColumnType::Int), spec("a", ColumnType::Text)];
        let byts = serialize_cells([val_int(123), val_str("abc")]);
        let row = deserialize::<MyRow<'_>>(specs, &byts).unwrap();
        assert_eq!(
            row,
            MyRow {
                a: "abc",
                b: Some(123),
                c: String::new(),
            }
        );

        // Missing column
        let specs = &[spec("a", ColumnType::Text)];
        MyRow::type_check(specs).unwrap_err();

        // Wrong column type
        let specs = &[spec("a", ColumnType::Int), spec("b", ColumnType::Int)];
        MyRow::type_check(specs).unwrap_err();
    }

    #[test]
    fn test_struct_deserialization_strict_ordering() {
        #[derive(DeserializeRow, PartialEq, Eq, Debug)]
        #[scylla(crate = "crate", enforce_order)]
        struct MyRow<'a> {
            a: &'a str,
            b: Option<i32>,
            #[scylla(skip)]
            c: String,
        }

        // Correct order of columns
        let specs = &[spec("a", ColumnType::Text), spec("b", ColumnType::Int)];
        let byts = serialize_cells([val_str("abc"), val_int(123)]);
        let row = deserialize::<MyRow<'_>>(specs, &byts).unwrap();
        assert_eq!(
            row,
            MyRow {
                a: "abc",
                b: Some(123),
                c: String::new(),
            }
        );

        // Wrong order of columns
        let specs = &[spec("b", ColumnType::Int), spec("a", ColumnType::Text)];
        MyRow::type_check(specs).unwrap_err();

        // Missing column
        let specs = &[spec("a", ColumnType::Text)];
        MyRow::type_check(specs).unwrap_err();

        // Wrong column type
        let specs = &[spec("a", ColumnType::Int), spec("b", ColumnType::Int)];
        MyRow::type_check(specs).unwrap_err();
    }

    fn val_int(i: i32) -> Option<Vec<u8>> {
        Some(i.to_be_bytes().to_vec())
    }

    fn val_str(s: &str) -> Option<Vec<u8>> {
        Some(s.as_bytes().to_vec())
    }

    fn spec(name: &str, typ: ColumnType) -> ColumnSpec {
        ColumnSpec {
            name: name.to_owned(),
            typ,
            table_spec: TableSpec {
                ks_name: "ks".to_owned(),
                table_name: "tbl".to_owned(),
            },
        }
    }

    fn deserialize<'frame, R>(
        specs: &'frame [ColumnSpec],
        byts: &'frame Bytes,
    ) -> Result<R, ParseError>
    where
        R: DeserializeRow<'frame>,
    {
        <R as DeserializeRow<'frame>>::type_check(specs)?;
        let slice = FrameSlice::new(byts);
        let iter = ColumnIterator::new(specs, slice);
        <R as DeserializeRow<'frame>>::deserialize(iter)
    }

    // TODO: Row iterator tests
}
