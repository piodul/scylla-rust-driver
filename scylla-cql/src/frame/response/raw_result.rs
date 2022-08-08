use super::result::{self, ColumnSpec, ColumnType, CqlValue};
use crate::frame::{frame_errors::ParseError, types};

pub struct RawValue<'rows> {
    pub typ: &'rows ColumnType,
    pub value: Option<&'rows [u8]>,
}

/// Iterator _over_ rows.
#[derive(Clone)]
pub struct RowIterator<'rows> {
    pub(crate) mem: &'rows [u8],
    pub(crate) col_specs: &'rows [ColumnSpec],
    pub(crate) remaining_rows: usize,
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
    pub(crate) row_iterator: RowIterator<'rows>,
    pub(crate) phantom_data: std::marker::PhantomData<RowT>,
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

macro_rules! impl_strict_type {
    ($cql_name:literal, $t:ty, $col_type:pat, $conv:expr) => {
        impl<'rows> DeserializableFromValue<'rows> for $t {
            type Target = $t;

            fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
                if !matches!(typ, $col_type) {
                    return Err(ParseError::BadData(format!(
                        "Expected {}, got {:?}",
                        $cql_name, typ
                    )));
                }
                Ok(())
            }

            fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
                let value = ensure_not_null(v.value)?;
                $conv(value)
            }
        }
    };
}

macro_rules! impl_fixed_numeric_type {
    ($cql_name:literal, $t:ty, $col_type:pat) => {
        impl_strict_type!($cql_name, $t, $col_type, |value| {
            const SIZE: usize = std::mem::size_of::<$t>();
            let arr = ensure_exact_length::<SIZE>($cql_name, value)?;
            Ok(<$t>::from_be_bytes(arr))
        });
    };
}

impl_strict_type!("boolean", bool, ColumnType::Boolean, |value| {
    let arr = ensure_exact_length::<1>("boolean", value)?;
    Ok(arr[0] != 0x00)
});

impl_fixed_numeric_type!("tinyint", i8, ColumnType::TinyInt);
impl_fixed_numeric_type!("smallint", i16, ColumnType::SmallInt);
impl_fixed_numeric_type!("int", i32, ColumnType::Int);
impl_fixed_numeric_type!("bigint", i64, ColumnType::BigInt); // TODO: Consider accepting counters here
impl_fixed_numeric_type!("float", f32, ColumnType::Float);
impl_fixed_numeric_type!("double", f64, ColumnType::Double);

impl_strict_type!("blob", &'rows [u8], ColumnType::Blob, Ok);
impl_strict_type!("blob", Vec<u8>, ColumnType::Blob, |value: &'rows [u8]| Ok(
    value.to_vec()
));

// &str or String may be created either from `text` or `ascii`,
// hence we cannot use impl_strict_type! for their impls.

// TODO: `Ascii` and `Utf8` strict types

impl<'rows> DeserializableFromValue<'rows> for &'rows str {
    type Target = &'rows str;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        ensure_string_type(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
        parse_string(v)
    }
}

impl<'rows> DeserializableFromValue<'rows> for String {
    type Target = String;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        ensure_string_type(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
        parse_string(v).map(str::to_string)
    }
}

fn ensure_string_type(typ: &ColumnType) -> Result<(), ParseError> {
    match typ {
        ColumnType::Ascii | ColumnType::Text => Ok(()),
        _ => Err(ParseError::BadData(format!(
            "Expected ascii or text, got {:?}",
            typ
        ))),
    }
}

fn parse_string(v: RawValue) -> Result<&str, ParseError> {
    let value = ensure_not_null(v.value)?;
    if matches!(v.typ, ColumnType::Ascii) && !value.is_ascii() {
        return Err(ParseError::BadData(
            "Expected a valid ASCII string".to_string(),
        ));
    }
    Ok(std::str::from_utf8(value)?)
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Date {
    days_since_epoch: i32,
}

impl Date {
    pub fn from_days_since_unix_epoch(days_since_epoch: i32) -> Self {
        Self { days_since_epoch }
    }

    pub fn from_naive_date(date: chrono::NaiveDate) -> Option<Self> {
        let days_since_epoch: i32 = date
            .signed_duration_since(chrono::NaiveDate::from_ymd(1970, 1, 1))
            .num_days()
            .try_into()
            .ok()?;
        Some(Self::from_days_since_unix_epoch(days_since_epoch))
    }

    pub fn to_days_since_unix_epoch(&self) -> i32 {
        self.days_since_epoch
    }

    // TODO: Consider a From/Into conversion
    pub fn to_naive_date(&self) -> Option<chrono::NaiveDate> {
        let days_since_epoch = chrono::Duration::days(self.days_since_epoch as i64);
        chrono::NaiveDate::from_ymd(1970, 1, 1).checked_add_signed(days_since_epoch)
    }
}

impl_strict_type!("date", Date, ColumnType::Date, |value| {
    let arr = ensure_exact_length::<4>("date", value)?;
    Ok(Date::from_days_since_unix_epoch(i32::from_be_bytes(arr)))
});

// TODO: Consider a "Decimal" structure

impl_strict_type!(
    "decimal",
    bigdecimal::BigDecimal,
    ColumnType::Decimal,
    |mut value| {
        let scale = types::read_int(&mut value)? as i64;
        let int_value = num_bigint::BigInt::from_signed_bytes_be(value);
        Ok(bigdecimal::BigDecimal::from((int_value, scale)))
    }
);

fn ensure_not_null(v: Option<&[u8]>) -> Result<&[u8], ParseError> {
    v.ok_or_else(|| ParseError::BadData("expected a non-null value".to_string()))
}

fn ensure_exact_length<const SIZE: usize>(
    cql_name: &str,
    v: &[u8],
) -> Result<[u8; SIZE], ParseError> {
    v.try_into().map_err(|_| {
        return ParseError::BadData(format!(
            "The type {} requires {} bytes, but got {}",
            cql_name,
            SIZE,
            v.len(),
        ));
    })
}
