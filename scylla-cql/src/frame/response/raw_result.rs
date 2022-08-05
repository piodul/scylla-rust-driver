use super::result::{self, ColumnSpec, ColumnType, CqlValue, ResultMetadata};
use crate::frame::{frame_errors::ParseError, types};
use bytes::Bytes;

pub struct RawRows {
    pub metadata: ResultMetadata,
    pub rows_count: usize,
    pub rows: Bytes,
}

pub struct RawValue<'rows> {
    pub typ: &'rows ColumnType,
    pub value: Option<&'rows [u8]>,
}

impl RawRows {
    pub fn into_rows(self) -> Result<result::Rows, ParseError> {
        type CellType = Option<CqlValue>;
        type RowType = Vec<CellType>;

        let rows = self
            .iter()
            .map(|row| {
                Ok(result::Row {
                    columns: RowType::deserialize(row?)?,
                })
            })
            .collect::<Result<Vec<_>, ParseError>>()?;

        Ok(result::Rows {
            metadata: self.metadata,
            rows_count: self.rows_count,
            rows,
        })
    }

    pub fn as_typed<'me, RowT: DeserializableFromRow<'me>>(
        &'me self,
    ) -> Result<TypedRowIterator<'me, RowT>, ParseError> {
        RowT::type_check(&self.metadata.col_specs)?;
        Ok(TypedRowIterator {
            row_iterator: self.iter(),
            phantom_data: Default::default(),
        })
    }

    pub fn iter(&self) -> RowIterator {
        RowIterator {
            mem: &*self.rows.0,
            col_specs: &self.metadata.col_specs,
            remaining_rows: self.rows_count,
        }
    }
}

/// Iterator _over_ rows.
#[derive(Clone)]
pub struct RowIterator<'rows> {
    mem: &'rows [u8],
    col_specs: &'rows [ColumnSpec],
    remaining_rows: usize,
}

impl<'rows> Iterator for RowIterator<'rows> {
    type Item = Result<ValueIterator<'rows>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.remaining_rows = self.remaining_rows.checked_sub(1)?;

        let prev_remaining_bytes = self.mem.len();
        let mut new_mem = &*self.mem;
        for _ in 0..self.col_specs.len() {
            if let Err(err) = types::read_bytes_opt(&mut new_mem) {
                self.remaining_rows = 0;
                return Some(Err(err));
            };
        }

        let row_bytes = prev_remaining_bytes - new_mem.len();

        let ret = ValueIterator {
            mem: &self.mem[..row_bytes],
            col_specs: self.col_specs,
        };
        self.mem = new_mem;

        Some(Ok(ret))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining_rows, Some(self.remaining_rows))
    }
}

#[derive(Clone)]
pub struct TypedRowIterator<'rows, RowT> {
    row_iterator: RowIterator<'rows>,
    phantom_data: std::marker::PhantomData<RowT>,
}

impl<'rows, RowT> Iterator for TypedRowIterator<'rows, RowT>
where
    RowT: DeserializableFromRow<'rows>,
{
    type Item = Result<RowT::Target, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.row_iterator
            .next()
            .map(|r| r.and_then(RowT::deserialize))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.row_iterator.size_hint()
    }
}

/// Iterator _over_ values.
#[derive(Clone)]
pub struct ValueIterator<'rows> {
    mem: &'rows [u8],
    col_specs: &'rows [ColumnSpec],
}

impl<'rows> Iterator for ValueIterator<'rows> {
    type Item = Result<RawValue<'rows>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.col_specs.is_empty() {
            return None;
        }

        types::read_bytes_opt(&mut self.mem)
            .map(|value| {
                let typ = &self.col_specs[0].typ;
                self.col_specs = &self.col_specs[1..];
                Some(RawValue { typ, value })
            })
            .transpose()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.col_specs.len();
        (remaining, Some(remaining))
    }
}

pub trait DeserializableFromRow<'rows>
where
    Self: Sized,
{
    /// Result of the deserialization. Usually, it can be just set to `Self`.
    /// However, sometimes it is useful to have different methods
    /// of deserialization which result in the same type.
    type Target: 'rows;

    /// Checks whether this type can be deserialized from given CQL type.
    fn type_check(typs: &[ColumnSpec]) -> Result<(), ParseError>;

    /// Deserialize from given bytes.
    /// The function may assume that `type_check` was called and it succeeded.
    /// The length of `typs` must always be the same as `vs`.
    fn deserialize(row: ValueIterator<'rows>) -> Result<Self::Target, ParseError>;
}

/// A value which can be deserialized from a single column
pub trait DeserializableFromValue<'rows>
where
    Self: Sized,
{
    /// Result of the deserialization. Usually, it can be just set to `Self`.
    /// However, sometimes it is useful to have different methods
    /// of deserialization which result in the same type, e.g. a "strict" `i64`
    /// which accepts only the "bigint" CQL type, or a more relaxed `RelaxedI64`
    /// which accepts any numeric type and returns an error on overflow.
    type Target: 'rows;

    /// Checks whether this type can be deserialized from given CQL type.
    fn type_check(typ: &ColumnType) -> Result<(), ParseError>;

    /// Deserialize from given bytes.
    /// The function may assume that `type_check` was called and it succeeded.
    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError>;
}

impl<'rows, T> DeserializableFromRow<'rows> for Vec<T>
where
    T: DeserializableFromValue<'rows>,
{
    type Target = Vec<T::Target>;

    fn type_check(typs: &[ColumnSpec]) -> Result<(), ParseError> {
        typs.iter().try_for_each(|spec| T::type_check(&spec.typ))
    }

    fn deserialize(row: ValueIterator<'rows>) -> Result<Self::Target, ParseError> {
        row.map(|v| v.and_then(T::deserialize)).collect()
    }
}

impl<'rows> DeserializableFromValue<'rows> for CqlValue {
    type Target = CqlValue;

    fn type_check(_typ: &ColumnType) -> Result<(), ParseError> {
        // All types are accepted
        Ok(())
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
        let mut value = ensure_not_null(v.value)?;
        result::deser_cql_value(v.typ, &mut value)
    }
}

impl<'rows, T> DeserializableFromValue<'rows> for Option<T>
where
    T: DeserializableFromValue<'rows> + 'rows,
{
    type Target = Option<T::Target>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        T::type_check(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
        v.value
            .map(|value| {
                T::deserialize(RawValue {
                    typ: v.typ,
                    value: Some(value),
                })
            })
            .transpose()
    }
}

// impl<'rows> DeserializableFromValue<'rows> for i8 {
//     type Target = i8;

//     fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
//         if !matches!(typ, ColumnType::TinyInt) {
//             return Err(ParseError("expected tinyint".to_string()));
//         }
//         Ok(())
//     }

//     fn deserialize(_v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
//         let v = ensure_not_null(v)?;
//         ensure_exact_length(v, 1)?;
//         Ok(v[0] as i8)
//     }
// }

fn ensure_not_null(v: Option<&[u8]>) -> Result<&[u8], ParseError> {
    v.ok_or_else(|| ParseError::BadData("expected a non-null value".to_string()))
}

// fn ensure_exact_length(v: &[u8], length: usize) -> Result<(), ParseError> {
//     if v.len() != length {
//         return Err(ParseError::BadData(format!(
//             "expected a value of {} bytes, got {}",
//             length,
//             v.len()
//         )));
//     }
//     Ok(())
// }
