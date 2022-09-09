use std::net::IpAddr;

// TODO: Need a VERY detailed comment describing the types available
// for deserialization

use super::result::{self, ColumnSpec, ColumnType, CqlValue};
use crate::frame::{
    frame_errors::ParseError,
    types,
    value::{CqlDuration, Date, Time, Timestamp},
};

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

macro_rules! impl_tuple_row {
    ($($Ti:ident),* ; $($FieldI:tt),*) => {
        impl<'rows, $($Ti),*> DeserializableFromRow<'rows> for ($($Ti,)*)
        where
            $($Ti: DeserializableFromValue<'rows>),*
        {
            type Target = (
                $(<$Ti as DeserializableFromValue<'rows>>::Target,)*
            );

            fn type_check(specs: &[ColumnSpec]) -> Result<(), ParseError> {
                const TUPLE_LEN: usize = [0, $($FieldI),*].len() - 1;
                if TUPLE_LEN != specs.len() {
                    return Err(ParseError::BadData(format!(
                        "Expected row size {:?}, but got {:?}",
                        TUPLE_LEN, specs.len(),
                    )));
                }

                // TODO: More context about which field had the wrong type
                // TODO: Does this result in runtime bound checking? Can we
                // rephrase the code so that it can't happen? (e.g. by matching
                // on an array)
                $(
                    <$Ti as DeserializableFromValue<'rows>>::type_check(&specs[$FieldI].typ)?;
                )*

                Ok(())
            }

            fn deserialize(mut row: ValueIterator<'rows>) -> Result<Self::Target, ParseError> {
                // TODO: More context about which column failed to deserialize

                const TUPLE_LEN: usize = [0, $($FieldI),*].len() - 1;
                let tup = (
                    $(
                        {
                            let cell = row.next()
                                .ok_or_else(|| ParseError::BadData(format!(
                                    "Row is too short, expected {:?} elements but only got {:?}",
                                    TUPLE_LEN, $FieldI,
                                )))??;
                            <$Ti as DeserializableFromValue<'rows>>::deserialize(cell)?
                        },
                    )*
                );
                if row.next().is_some() {
                    return Err(ParseError::BadData(format!(
                        "Row is too long, expected {:?} elements but it got more",
                        TUPLE_LEN,
                    )));
                }
                Ok(tup)
            }
        }
    };
}

macro_rules! impl_tuples_row {
    ($TN:ident ; $FieldN:tt) => {
        impl_tuple_row!( ; );
        impl_tuple_row!($TN ; $FieldN);
    };
    ($TN:ident, $($Ti:ident),* ; $FieldN:tt, $($FieldI:tt),*) => {
        impl_tuples_row!($($Ti),* ; $($FieldI),*);
        impl_tuple_row!($TN, $($Ti),* ; $FieldN, $($FieldI),*);
    };
}

impl_tuples_row!(
    T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15;
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
);

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
impl_strict_type!("blob", Vec<u8>, ColumnType::Blob, |value: &'_ [u8]| Ok(
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

impl_strict_type!("date", Date, ColumnType::Date, |value| {
    let arr = ensure_exact_length::<4>("date", value)?;
    let days = (i32::from_be_bytes(arr) as u32).wrapping_add(1 << 31);
    Ok(Date(days))
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

impl_strict_type!(
    "duration",
    CqlDuration,
    ColumnType::Duration,
    |mut value| {
        let months = i32::try_from(types::vint_decode(&mut value)?)?;
        let days = i32::try_from(types::vint_decode(&mut value)?)?;
        let nanoseconds = types::vint_decode(&mut value)?;

        // TODO: Verify that there are no bytes remaining

        Ok(CqlDuration {
            months,
            days,
            nanoseconds,
        })
    }
);

impl_strict_type!("timestamp", Timestamp, ColumnType::Timestamp, |value| {
    let arr = ensure_exact_length::<8>("date", value)?;
    let duration = chrono::Duration::milliseconds(i64::from_be_bytes(arr));
    Ok(Timestamp(duration))
});

impl_strict_type!("time", Time, ColumnType::Time, |value| {
    let arr = ensure_exact_length::<8>("date", value)?;
    let nanoseconds = i64::from_be_bytes(arr);

    // Valid values are in the range 0 to 86399999999999
    if !(0..=86399999999999).contains(&nanoseconds) {
        return Err(ParseError::BadData(format! {
            "Invalid time value only 0 to 86399999999999 allowed: {}.", nanoseconds,
        }));
    }

    Ok(Time(chrono::Duration::nanoseconds(nanoseconds)))
});

impl_strict_type!("inet", IpAddr, ColumnType::Inet, |value: &'_ [u8]| {
    if let Ok(ipv4) = <[u8; 4]>::try_from(value) {
        Ok(IpAddr::from(ipv4))
    } else if let Ok(ipv16) = <[u8; 16]>::try_from(value) {
        Ok(IpAddr::from(ipv16))
    } else {
        Err(ParseError::BadData(format!(
            "Invalid inet bytes length: {}",
            value.len()
        )))
    }
});

// Here, uuid works both with timeuuid and uuid
// TODO: Consider adding separate types

impl<'rows> DeserializableFromValue<'rows> for uuid::Uuid {
    type Target = uuid::Uuid;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        match typ {
            ColumnType::Timeuuid | ColumnType::Uuid => Ok(()),
            _ => Err(ParseError::BadData(format!(
                "Expected timeuuid or uuid, got {:?}",
                typ,
            ))),
        }
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
        let value = ensure_not_null(v.value)?;
        let arr = ensure_exact_length::<16>("timeuuid/uuid", value)?;
        let i = u128::from_be_bytes(arr);
        Ok(uuid::Uuid::from_u128(i))
    }
}

// Compound types follow

// Set and List
pub struct SequenceIterator<'rows, T> {
    remaining: usize,
    mem: &'rows [u8],
    el_type: &'rows ColumnType,
    phantom_data: std::marker::PhantomData<T>,
}

impl<'rows, T> DeserializableFromValue<'rows> for SequenceIterator<'rows, T>
where
    T: DeserializableFromValue<'rows> + 'rows,
{
    type Target = SequenceIterator<'rows, T>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        ensure_sequence_type::<T>(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
        let mut value = ensure_not_null(v.value)?;
        let count = types::read_int_length(&mut value)?;
        let el_type = match &v.typ {
            ColumnType::Set(el) | ColumnType::List(el) => el,
            _ => return Err(ParseError::BadData("not a collection".to_string())),
        };
        Ok(Self {
            remaining: count,
            mem: value,
            el_type,
            phantom_data: std::marker::PhantomData,
        })
    }
}

impl<'rows, T> Iterator for SequenceIterator<'rows, T>
where
    T: DeserializableFromValue<'rows> + 'rows,
{
    type Item = Result<<T as DeserializableFromValue<'rows>>::Target, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            None
        } else {
            self.remaining -= 1;
            Some(types::read_bytes_opt(&mut self.mem).and_then(|mem| {
                let rv = RawValue {
                    typ: self.el_type,
                    value: mem,
                };
                <T as DeserializableFromValue<'rows>>::deserialize(rv)
            }))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'rows, T> DeserializableFromValue<'rows> for Vec<T>
where
    T: DeserializableFromValue<'rows> + 'rows,
{
    type Target = Vec<<T as DeserializableFromValue<'rows>>::Target>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        ensure_sequence_type::<T>(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
        let iter = SequenceIterator::<'rows, T>::deserialize(v)?;
        iter.collect()
    }
}

// Maps
pub struct MapIterator<'rows, K, V> {
    remaining: usize,
    mem: &'rows [u8],
    key_type: &'rows ColumnType,
    value_type: &'rows ColumnType,
    phantom_data: std::marker::PhantomData<(K, V)>,
}

impl<'rows, K, V> DeserializableFromValue<'rows> for MapIterator<'rows, K, V>
where
    K: DeserializableFromValue<'rows> + 'rows,
    V: DeserializableFromValue<'rows> + 'rows,
{
    type Target = MapIterator<'rows, K, V>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        ensure_map_type::<K, V>(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self::Target, ParseError> {
        let mut value = ensure_not_null(v.value)?;
        let count = types::read_int_length(&mut value)?;
        let (key_type, value_type) = match &v.typ {
            ColumnType::Map(k, v) => (k, v),
            _ => return Err(ParseError::BadData("not a map".to_string())),
        };
        Ok(Self {
            remaining: count,
            mem: value,
            key_type,
            value_type,
            phantom_data: std::marker::PhantomData,
        })
    }
}

impl<'rows, K, V> Iterator for MapIterator<'rows, K, V>
where
    K: DeserializableFromValue<'rows> + 'rows,
    V: DeserializableFromValue<'rows> + 'rows,
{
    type Item = Result<
        (
            <K as DeserializableFromValue<'rows>>::Target,
            <V as DeserializableFromValue<'rows>>::Target,
        ),
        ParseError,
    >;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            None
        } else {
            self.remaining -= 1;
            let mut parse_pair = || -> Self::Item {
                let key_rv = RawValue {
                    typ: self.key_type,
                    value: types::read_bytes_opt(&mut self.mem)?,
                };
                let key = K::deserialize(key_rv)?;
                let value_rv = RawValue {
                    typ: self.value_type,
                    value: types::read_bytes_opt(&mut self.mem)?,
                };
                let value = V::deserialize(value_rv)?;
                Ok((key, value))
            };
            Some(parse_pair())
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

// TODO: Conversion to HashMap, BTreeMap, etc.?

// TODO: UDTs
// TODO: Tuples
// The above should be automatically with proc or non-proc macros

fn ensure_sequence_type<'rows, T>(typ: &ColumnType) -> Result<(), ParseError>
where
    T: DeserializableFromValue<'rows>,
{
    // TODO: Add more information to context in case the type check fails
    match typ {
        ColumnType::List(el) | ColumnType::Set(el) => T::type_check(el),
        _ => Err(ParseError::BadData(format!(
            "Expected set or list, got {:?}",
            typ
        ))),
    }
}

fn ensure_map_type<'rows, K, V>(typ: &ColumnType) -> Result<(), ParseError>
where
    K: DeserializableFromValue<'rows>,
    V: DeserializableFromValue<'rows>,
{
    // TODO: Add more information to context in case the type check fails
    match typ {
        ColumnType::Map(k, v) => {
            K::type_check(k)?;
            V::type_check(v)?;
            Ok(())
        }
        _ => Err(ParseError::BadData(format!("Expected map, fot {:?}", typ))),
    }
}

fn ensure_not_null(v: Option<&[u8]>) -> Result<&[u8], ParseError> {
    v.ok_or_else(|| ParseError::BadData("expected a non-null value".to_string()))
}

fn ensure_exact_length<const SIZE: usize>(
    cql_name: &str,
    v: &[u8],
) -> Result<[u8; SIZE], ParseError> {
    v.try_into().map_err(|_| {
        ParseError::BadData(format!(
            "The type {} requires {} bytes, but got {}",
            cql_name,
            SIZE,
            v.len(),
        ))
    })
}
