use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::{BuildHasher, Hash};
use std::net::IpAddr;

use bytes::Bytes;
use uuid::Uuid;

use crate::frame::frame_errors::ParseError;
use crate::frame::response::result::{deser_cql_value, ColumnType, CqlValue};
use crate::frame::types;
use crate::frame::value::{CqlDuration, Date, Time, Timestamp};

use super::RawValue;

/// A value which can be deserialized from a single column
pub trait FromCql<'rows>
where
    Self: Sized,
{
    /// Checks whether this type can be deserialized from given CQL type.
    fn type_check(typ: &ColumnType) -> Result<(), ParseError>;

    /// Deserialize from given bytes.
    /// The function may assume that `type_check` was called and it succeeded.
    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError>;
}

impl<'rows> FromCql<'rows> for RawValue<'rows> {
    fn type_check(_typ: &ColumnType) -> Result<(), ParseError> {
        Ok(())
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        Ok(v)
    }
}

impl<'rows> FromCql<'rows> for CqlValue {
    fn type_check(_typ: &ColumnType) -> Result<(), ParseError> {
        // Type checking is done in deserialize
        Ok(())
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        let mut val = ensure_not_null(v)?;
        let cql = deser_cql_value(v.typ, &mut val)?;
        Ok(cql)
    }
}

impl<'rows, T> FromCql<'rows> for Option<T>
where
    T: FromCql<'rows>,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        T::type_check(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        v.value.map(|_| T::deserialize(v)).transpose()
    }
}

macro_rules! impl_strict_type {
    ($cql_name:literal, $t:ty, $cql_type:pat, $conv:expr) => {
        impl<'rows> FromCql<'rows> for $t {
            fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
                // TODO: Print the CQL type name from ColumnType
                // in the notation that Cassandra uses
                match typ {
                    $cql_type => Ok(()),
                    _ => Err(ParseError::BadIncomingData(format!(
                        "Expected {}, got {:?}",
                        $cql_name, typ,
                    ))),
                }
            }

            fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
                $conv(v)
            }
        }
    };
}

// fixed numeric types

macro_rules! impl_fixed_numeric_type {
    ($cql_name:literal, $t:ty, $col_type:pat) => {
        impl_strict_type!($cql_name, $t, $col_type, |v: RawValue<'rows>| {
            const SIZE: usize = std::mem::size_of::<$t>();
            let val = ensure_not_null(v)?;
            let arr = ensure_exact_length::<SIZE>($cql_name, val)?;
            Ok(<$t>::from_be_bytes(arr))
        });
    };
}

impl_strict_type!("boolean", bool, ColumnType::Boolean, |v: RawValue<
    'rows,
>| {
    let val = ensure_not_null(v)?;
    let arr = ensure_exact_length::<1>("boolean", val)?;
    Ok(arr[0] != 0x00)
});

impl_fixed_numeric_type!("tinyint", i8, ColumnType::TinyInt);
impl_fixed_numeric_type!("smallint", i16, ColumnType::SmallInt);
impl_fixed_numeric_type!("int", i32, ColumnType::Int);
impl_fixed_numeric_type!(
    "bigint or counter",
    i64,
    ColumnType::BigInt | ColumnType::Counter
);
impl_fixed_numeric_type!("float", f32, ColumnType::Float);
impl_fixed_numeric_type!("double", f64, ColumnType::Double);

// other numeric types

impl_strict_type!(
    "varint",
    num_bigint::BigInt,
    ColumnType::BigInt,
    |v: RawValue<'rows>| {
        let val = ensure_not_null(v)?;
        Ok(num_bigint::BigInt::from_signed_bytes_be(val))
    }
);

impl_strict_type!(
    "decimal",
    bigdecimal::BigDecimal,
    ColumnType::Decimal,
    |v: RawValue<'rows>| {
        let mut val = ensure_not_null(v)?;
        let scale = types::read_int(&mut val)? as i64;
        let int_value = num_bigint::BigInt::from_signed_bytes_be(val);
        Ok(bigdecimal::BigDecimal::from((int_value, scale)))
    }
);

// blob

impl_strict_type!("blob", &'rows [u8], ColumnType::Blob, |v: RawValue<
    'rows,
>| {
    let val = ensure_not_null(v)?;
    Ok(val)
});
impl_strict_type!("blob", Vec<u8>, ColumnType::Blob, |v: RawValue<'rows>| {
    let val = ensure_not_null(v)?;
    Ok(val.to_vec())
});
impl_strict_type!("blob", Bytes, ColumnType::Blob, |v: RawValue<'rows>| {
    let val = ensure_not_null_owned(v)?;
    Ok(val)
});

// string
// TODO: Types which accept only ascii or text

macro_rules! impl_string_type {
    ($t:ty, $conv:expr) => {
        impl_strict_type!(
            "ascii or text",
            $t,
            ColumnType::Ascii | ColumnType::Text,
            $conv
        );
    };
}

impl_string_type!(&'rows str, |v: RawValue<'rows>| {
    let val = ensure_not_null(v)?;
    check_ascii(v.typ, val)?;
    Ok(std::str::from_utf8(val)?)
});
impl_string_type!(String, |v: RawValue<'rows>| {
    let val = ensure_not_null(v)?;
    check_ascii(v.typ, val)?;
    Ok(std::str::from_utf8(val)?.to_string())
});

// TODO: Deserialization for string::String<Bytes>

fn check_ascii(typ: &ColumnType, s: &[u8]) -> Result<(), ParseError> {
    if matches!(typ, ColumnType::Ascii) && !s.is_ascii() {
        return Err(ParseError::BadIncomingData(
            "Expected a valid ASCII string".to_string(),
        ));
    }
    Ok(())
}

// date and time types

impl_strict_type!("date", Date, ColumnType::Date, |v: RawValue<'rows>| {
    let val = ensure_not_null(v)?;
    let arr = ensure_exact_length::<4>("date", val)?;
    let days = (i32::from_be_bytes(arr) as u32).wrapping_add(1 << 31);
    Ok(Date(days))
});

impl_strict_type!(
    "duration",
    CqlDuration,
    ColumnType::Duration,
    |v: RawValue<'rows>| {
        let mut val = ensure_not_null(v)?;
        let months = i32::try_from(types::vint_decode(&mut val)?)?;
        let days = i32::try_from(types::vint_decode(&mut val)?)?;
        let nanoseconds = types::vint_decode(&mut val)?;

        // TODO: Verify that there are no bytes remaining

        Ok(CqlDuration {
            months,
            days,
            nanoseconds,
        })
    }
);

impl_strict_type!(
    "timestamp",
    Timestamp,
    ColumnType::Timestamp,
    |v: RawValue<'rows>| {
        let val = ensure_not_null(v)?;
        let arr = ensure_exact_length::<8>("date", val)?;
        let duration = chrono::Duration::milliseconds(i64::from_be_bytes(arr));
        Ok(Timestamp(duration))
    }
);

impl_strict_type!("time", Time, ColumnType::Time, |v: RawValue<'rows>| {
    let val = ensure_not_null(v)?;
    let arr = ensure_exact_length::<8>("date", val)?;
    let nanoseconds = i64::from_be_bytes(arr);

    // Valid values are in the range 0 to 86399999999999
    if !(0..=86399999999999).contains(&nanoseconds) {
        return Err(ParseError::BadIncomingData(format! {
            "Invalid time value only 0 to 86399999999999 allowed: {}.", nanoseconds,
        }));
    }

    Ok(Time(chrono::Duration::nanoseconds(nanoseconds)))
});

// inet

impl_strict_type!("inet", IpAddr, ColumnType::Inet, |v: RawValue<'rows>| {
    let val = ensure_not_null(v)?;
    if let Ok(ipv4) = <[u8; 4]>::try_from(val) {
        Ok(IpAddr::from(ipv4))
    } else if let Ok(ipv16) = <[u8; 16]>::try_from(val) {
        Ok(IpAddr::from(ipv16))
    } else {
        Err(ParseError::BadIncomingData(format!(
            "Invalid inet bytes length: {}",
            val.len(),
        )))
    }
});

// uuid
// TODO: Consider having separate types for timeuuid and uuid

impl_strict_type!(
    "timeuuid or uuid",
    Uuid,
    ColumnType::Uuid | ColumnType::Timeuuid,
    |v: RawValue<'rows>| {
        let val = ensure_not_null(v)?;
        let arr = ensure_exact_length::<16>("timeuuid or uuid", val)?;
        let i = u128::from_be_bytes(arr);
        Ok(uuid::Uuid::from_u128(i))
    }
);

/// A value that may be empty or not.
///
/// In CQL, some types can have a special value of "empty", represented as
/// a serialized value of length 0. Notably, this is a different value
/// than "null" as the latter is represented as a value with negative length.
/// An example of this are integral types: the "int" type can actually
/// hold 2^32 + 1 possible values because of this quirk.
///
/// `MaybeEmpty` was added in order to support this quirk. The `FromCql` trait
/// is implemented for each `MaybeEmpty<T>` where `T` is a CQL type that
/// can be empty.
pub enum MaybeEmpty<T> {
    Empty,
    Value(T),
}

/// A marker trait for types that can have an "empty" value in CQL.
pub trait EmptyableValue {}

impl<'rows, T> FromCql<'rows> for MaybeEmpty<T>
where
    T: FromCql<'rows> + EmptyableValue,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        <T as FromCql<'rows>>::type_check(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        let val = ensure_not_null(v)?;
        if val.is_empty() {
            Ok(MaybeEmpty::Empty)
        } else {
            let v = <T as FromCql<'rows>>::deserialize(v)?;
            Ok(MaybeEmpty::Value(v))
        }
    }
}

impl EmptyableValue for i8 {}
impl EmptyableValue for i16 {}
impl EmptyableValue for i32 {}
impl EmptyableValue for i64 {}
impl EmptyableValue for f32 {}
impl EmptyableValue for f64 {}
// TODO: Add the rest of emptyable values

// collections

// lists and sets

// TODO: Split into iterator for list and set?
pub struct SequenceIterator<'rows, T> {
    remaining_count: usize,
    elem_typ: &'rows ColumnType,
    mem: &'rows [u8],
    original_bytes: &'rows Bytes,
    phantom_data: std::marker::PhantomData<T>,
}

impl<'rows, T> SequenceIterator<'rows, T> {
    pub fn new(
        count: usize,
        elem_typ: &'rows ColumnType,
        mem: &'rows [u8],
        original_bytes: &'rows Bytes,
    ) -> Self {
        Self {
            remaining_count: count,
            elem_typ,
            mem,
            original_bytes,
            phantom_data: std::marker::PhantomData,
        }
    }
}

impl<'rows, T> FromCql<'rows> for SequenceIterator<'rows, T>
where
    T: FromCql<'rows>,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        match typ {
            ColumnType::List(el_t) | ColumnType::Set(el_t) => {
                <T as FromCql<'rows>>::type_check(el_t)
            }
            _ => Err(ParseError::BadIncomingData(format!(
                "Expected list or set, got {:?}",
                typ,
            ))),
        }
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        let mut mem = ensure_not_null(v)?;
        let count = types::read_int_length(&mut mem)?;
        let elem_typ = match v.typ() {
            ColumnType::List(elem_typ) | ColumnType::Set(elem_typ) => elem_typ,
            _ => {
                return Err(ParseError::BadIncomingData(format!(
                    "Expected list or set, got {:?}",
                    v.typ(),
                )))
            }
        };
        Ok(Self::new(count, elem_typ, mem, v.original_bytes()))
    }
}

impl<'rows, T> Iterator for SequenceIterator<'rows, T>
where
    T: FromCql<'rows>,
{
    type Item = Result<T, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.remaining_count = self.remaining_count.checked_sub(1)?;
        Some(parse_next_value(
            &mut self.mem,
            self.elem_typ,
            self.original_bytes,
        ))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.remaining_count))
    }
}

// TODO: Can we implement FromCql for every type that can collect from an iter?
// I'm not sure it is possible, there will be conflicts with MapIterator
// and collections of pairs

impl<'rows, T> FromCql<'rows> for Vec<T>
where
    T: FromCql<'rows>,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        SequenceIterator::<'rows, T>::type_check(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        SequenceIterator::<'rows, T>::deserialize(v)?.collect()
    }
}

impl<'rows, T> FromCql<'rows> for BTreeSet<T>
where
    T: FromCql<'rows> + Ord,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        SequenceIterator::<'rows, T>::type_check(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        SequenceIterator::<'rows, T>::deserialize(v)?.collect()
    }
}

impl<'rows, T, S> FromCql<'rows> for HashSet<T, S>
where
    T: FromCql<'rows> + Eq + Hash,
    S: BuildHasher + Default,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        SequenceIterator::<'rows, T>::type_check(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        SequenceIterator::<'rows, T>::deserialize(v)?.collect()
    }
}

pub struct MapIterator<'rows, K, V> {
    remaining_count: usize,
    k_typ: &'rows ColumnType,
    v_typ: &'rows ColumnType,
    mem: &'rows [u8],
    original_bytes: &'rows Bytes,
    phantom_data_k: std::marker::PhantomData<K>,
    phantom_data_v: std::marker::PhantomData<V>,
}

impl<'rows, K, V> FromCql<'rows> for MapIterator<'rows, K, V>
where
    K: FromCql<'rows>,
    V: FromCql<'rows>,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        match typ {
            ColumnType::Map(k_t, v_t) => {
                <K as FromCql<'rows>>::type_check(k_t)?;
                <V as FromCql<'rows>>::type_check(v_t)?;
                Ok(())
            }
            _ => Err(ParseError::BadIncomingData(format!(
                "Expected map, got {:?}",
                typ,
            ))),
        }
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        let mut mem = ensure_not_null(v)?;
        let count = types::read_int_length(&mut mem)?;
        let (k_typ, v_typ) = match v.typ() {
            ColumnType::Map(k_t, v_t) => (k_t, v_t),
            _ => {
                return Err(ParseError::BadIncomingData(format!(
                    "Expected map, got {:?}",
                    v.typ(),
                )))
            }
        };
        Ok(Self {
            remaining_count: count,
            k_typ,
            v_typ,
            mem,
            original_bytes: v.original_bytes(),
            phantom_data_k: std::marker::PhantomData,
            phantom_data_v: std::marker::PhantomData,
        })
    }
}

impl<'rows, K, V> Iterator for MapIterator<'rows, K, V>
where
    K: FromCql<'rows>,
    V: FromCql<'rows>,
{
    type Item = Result<(K, V), ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.remaining_count = self.remaining_count.checked_sub(1)?;
        let mut do_next = || -> Result<(K, V), ParseError> {
            let k = parse_next_value(&mut self.mem, self.k_typ, self.original_bytes)?;
            let v = parse_next_value(&mut self.mem, self.v_typ, self.original_bytes)?;
            Ok((k, v))
        };
        do_next().map(Some).transpose()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.remaining_count))
    }
}

impl<'rows, K, V> FromCql<'rows> for BTreeMap<K, V>
where
    K: FromCql<'rows> + Ord,
    V: FromCql<'rows>,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        MapIterator::<'rows, K, V>::type_check(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        MapIterator::<'rows, K, V>::deserialize(v)?.collect()
    }
}

impl<'rows, K, V, S> FromCql<'rows> for HashMap<K, V, S>
where
    K: FromCql<'rows> + Eq + Hash,
    V: FromCql<'rows>,
    S: BuildHasher + Default,
{
    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        MapIterator::<'rows, K, V>::type_check(typ)
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        MapIterator::<'rows, K, V>::deserialize(v)?.collect()
    }
}

// tuples

// Implements tuple deserialization.
// The generated impl expects that the serialized data will contain EXACTLY
// the given amount of values.
// TODO: Offer more flexible, compatible options
macro_rules! impl_tuple {
    ($($Ti:ident),*; $($idx:literal),*; $($idf:ident),*) => {
        impl<'rows, $($Ti),*> FromCql<'rows> for ($($Ti,)*)
        where
            $($Ti: FromCql<'rows>),*
        {
            fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
                if let ColumnType::Tuple(typs_v) = typ {
                    if let [$($idf),*] = <Vec<ColumnType> as AsRef<[ColumnType]>>::as_ref(typs_v) {
                        $(
                            <$Ti as FromCql<'rows>>::type_check($idf)?;
                        )*
                        return Ok(());
                    }
                }
                const TUPLE_LEN: usize = [0, $($idx),*].len() - 1;
                return Err(ParseError::BadIncomingData(format!(
                    "Expected tuple of size {}, but got {:?}",
                    TUPLE_LEN, typ,
                )));
            }

            fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
                // Ignore the warning for the zero-sized tuple
                #[allow(unused_mut)]
                let mut val = ensure_not_null(v)?;
                let ret = (
                    $(
                        parse_next_value::<$Ti>(&mut val, v.typ(), v.original_bytes())?,
                    )*
                );
                if !val.is_empty() {
                    return Err(ParseError::BadIncomingData(
                        "Encoded tuple contains more value than the tuple type can hold".to_string(),
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

// Utilities

fn ensure_not_null<'rows>(v: RawValue<'rows>) -> Result<&[u8], ParseError> {
    v.value()
        .ok_or_else(|| ParseError::BadIncomingData("Expected a non-null value".to_string()))
}

fn ensure_not_null_owned<'rows>(v: RawValue<'rows>) -> Result<Bytes, ParseError> {
    v.value_owned()
        .ok_or_else(|| ParseError::BadIncomingData("Expected a non-null value".to_string()))
}

fn ensure_exact_length<const SIZE: usize>(
    cql_name: &str,
    v: &[u8],
) -> Result<[u8; SIZE], ParseError> {
    v.try_into().map_err(|_| {
        ParseError::BadIncomingData(format!(
            "The type {} requires {} bytes, but got {}",
            cql_name,
            SIZE,
            v.len(),
        ))
    })
}

fn parse_next_value<'rows, T>(
    mem: &mut &'rows [u8],
    typ: &'rows ColumnType,
    original_bytes: &'rows Bytes,
) -> Result<T, ParseError>
where
    T: FromCql<'rows>,
{
    let bytes = types::read_bytes_opt(mem)?;
    let value = RawValue::new(typ, bytes, original_bytes);
    <T as FromCql<'rows>>::deserialize(value)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

    use bytes::{BufMut, Bytes, BytesMut};
    use uuid::Uuid;

    use crate::frame::frame_errors::ParseError;
    use crate::frame::response::result::ColumnType;
    use crate::frame::types;
    use crate::types::deserialize::RawValue;

    use super::{FromCql, MapIterator, SequenceIterator};

    #[test]
    fn test_deserialize_bytes() {
        const ORIGINAL_BYTES: &[u8] = &[1, 5, 2, 4, 3];

        let bytes = make_cell(ORIGINAL_BYTES);

        let decoded_slice = deserialize::<&[u8]>(&ColumnType::Blob, &bytes).unwrap();
        let decoded_vec = deserialize::<Vec<u8>>(&ColumnType::Blob, &bytes).unwrap();
        let decoded_bytes = deserialize::<Bytes>(&ColumnType::Blob, &bytes).unwrap();

        assert_eq!(decoded_slice, ORIGINAL_BYTES);
        assert_eq!(decoded_vec, ORIGINAL_BYTES);
        assert_eq!(decoded_bytes, ORIGINAL_BYTES);
    }

    #[test]
    fn test_deserialize_ascii() {
        const ASCII_TEXT: &str = "The quick, brown fox jumps over the lazy dog";

        let ascii = make_cell(ASCII_TEXT.as_bytes());

        let decoded_ascii_str = deserialize::<&str>(&ColumnType::Ascii, &ascii).unwrap();
        let decoded_ascii_string = deserialize::<String>(&ColumnType::Ascii, &ascii).unwrap();
        let decoded_text_str = deserialize::<&str>(&ColumnType::Text, &ascii).unwrap();
        let decoded_text_string = deserialize::<String>(&ColumnType::Text, &ascii).unwrap();

        assert_eq!(decoded_ascii_str, ASCII_TEXT);
        assert_eq!(decoded_ascii_string, ASCII_TEXT);
        assert_eq!(decoded_text_str, ASCII_TEXT);
        assert_eq!(decoded_text_string, ASCII_TEXT);
    }

    #[test]
    fn test_deserialize_text() {
        const UNICODE_TEXT: &str = "Zażółć gęślą jaźń";

        let unicode = make_cell(UNICODE_TEXT.as_bytes());

        // Should fail because it's not an ASCII string
        deserialize::<&str>(&ColumnType::Ascii, &unicode).unwrap_err();
        deserialize::<String>(&ColumnType::Ascii, &unicode).unwrap_err();

        let decoded_text_str = deserialize::<&str>(&ColumnType::Text, &unicode).unwrap();
        let decoded_text_string = deserialize::<String>(&ColumnType::Text, &unicode).unwrap();
        assert_eq!(decoded_text_str, UNICODE_TEXT);
        assert_eq!(decoded_text_string, UNICODE_TEXT);
    }

    #[test]
    fn test_integral() {
        let tinyint = make_cell(&[0x01]);
        let decoded_tinyint = deserialize::<i8>(&ColumnType::TinyInt, &tinyint).unwrap();
        assert_eq!(decoded_tinyint, 0x01);

        let smallint = make_cell(&[0x01, 0x02]);
        let decoded_smallint = deserialize::<i16>(&ColumnType::SmallInt, &smallint).unwrap();
        assert_eq!(decoded_smallint, 0x0102);

        let int = make_cell(&[0x01, 0x02, 0x03, 0x04]);
        let decoded_int = deserialize::<i32>(&ColumnType::Int, &int).unwrap();
        assert_eq!(decoded_int, 0x01020304);

        let bigint = make_cell(&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);
        let decoded_bigint = deserialize::<i64>(&ColumnType::BigInt, &bigint).unwrap();
        assert_eq!(decoded_bigint, 0x0102030405060708);
    }

    #[test]
    fn test_floating_point() {
        let float = make_cell(&[63, 0, 0, 0]);
        let decoded_float = deserialize::<f32>(&ColumnType::Float, &float).unwrap();
        assert_eq!(decoded_float, 0.5);

        let double = make_cell(&[64, 0, 0, 0, 0, 0, 0, 0]);
        let decoded_double = deserialize::<f64>(&ColumnType::Double, &double).unwrap();
        assert_eq!(decoded_double, 2.0);
    }

    #[test]
    fn test_list_and_set() {
        let mut collection_contents = BytesMut::new();
        collection_contents.put_i32(3);
        append_cell(&mut collection_contents, "quick".as_bytes());
        append_cell(&mut collection_contents, "brown".as_bytes());
        append_cell(&mut collection_contents, "fox".as_bytes());

        let collection = make_cell(&collection_contents);

        let list_typ = ColumnType::List(Box::new(ColumnType::Ascii));
        let set_typ = ColumnType::List(Box::new(ColumnType::Ascii));

        // iterator
        let mut iter = deserialize::<SequenceIterator<&str>>(&list_typ, &collection).unwrap();
        assert_eq!(iter.next().transpose().unwrap(), Some("quick"));
        assert_eq!(iter.next().transpose().unwrap(), Some("brown"));
        assert_eq!(iter.next().transpose().unwrap(), Some("fox"));
        assert_eq!(iter.next().transpose().unwrap(), None);

        let expected_vec_str = vec!["quick", "brown", "fox"];
        let expected_vec_string = vec!["quick".to_string(), "brown".to_string(), "fox".to_string()];

        // list
        let decoded_vec_str = deserialize::<Vec<&str>>(&list_typ, &collection).unwrap();
        let decoded_vec_string = deserialize::<Vec<String>>(&list_typ, &collection).unwrap();
        assert_eq!(decoded_vec_str, expected_vec_str);
        assert_eq!(decoded_vec_string, expected_vec_string);

        // hash set
        let decoded_hash_str = deserialize::<HashSet<&str>>(&set_typ, &collection).unwrap();
        let decoded_hash_string = deserialize::<HashSet<String>>(&set_typ, &collection).unwrap();
        assert_eq!(
            decoded_hash_str,
            expected_vec_str.clone().into_iter().collect(),
        );
        assert_eq!(
            decoded_hash_string,
            expected_vec_string.clone().into_iter().collect(),
        );

        // btree set
        let decoded_btree_str = deserialize::<BTreeSet<&str>>(&set_typ, &collection).unwrap();
        let decoded_btree_string = deserialize::<BTreeSet<String>>(&set_typ, &collection).unwrap();
        assert_eq!(
            decoded_btree_str,
            expected_vec_str.clone().into_iter().collect(),
        );
        assert_eq!(
            decoded_btree_string,
            expected_vec_string.clone().into_iter().collect(),
        );
    }

    #[test]
    fn test_map() {
        let mut collection_contents = BytesMut::new();
        collection_contents.put_i32(3);
        append_cell(&mut collection_contents, &1i32.to_be_bytes());
        append_cell(&mut collection_contents, "quick".as_bytes());
        append_cell(&mut collection_contents, &2i32.to_be_bytes());
        append_cell(&mut collection_contents, "brown".as_bytes());
        append_cell(&mut collection_contents, &3i32.to_be_bytes());
        append_cell(&mut collection_contents, "fox".as_bytes());

        let collection = make_cell(&collection_contents);

        let typ = ColumnType::Map(Box::new(ColumnType::Int), Box::new(ColumnType::Ascii));

        // iterator
        let mut iter = deserialize::<MapIterator<i32, &str>>(&typ, &collection).unwrap();
        assert_eq!(iter.next().transpose().unwrap(), Some((1, "quick")));
        assert_eq!(iter.next().transpose().unwrap(), Some((2, "brown")));
        assert_eq!(iter.next().transpose().unwrap(), Some((3, "fox")));
        assert_eq!(iter.next().transpose().unwrap(), None);

        let expected_str = vec![(1, "quick"), (2, "brown"), (3, "fox")];
        let expected_string = vec![
            (1, "quick".to_string()),
            (2, "brown".to_string()),
            (3, "fox".to_string()),
        ];

        // hash set
        let decoded_hash_str = deserialize::<HashMap<i32, &str>>(&typ, &collection).unwrap();
        let decoded_hash_string = deserialize::<HashMap<i32, String>>(&typ, &collection).unwrap();
        assert_eq!(decoded_hash_str, expected_str.clone().into_iter().collect());
        assert_eq!(
            decoded_hash_string,
            expected_string.clone().into_iter().collect(),
        );

        // btree set
        let decoded_btree_str = deserialize::<BTreeMap<i32, &str>>(&typ, &collection).unwrap();
        let decoded_btree_string = deserialize::<BTreeMap<i32, String>>(&typ, &collection).unwrap();
        assert_eq!(
            decoded_btree_str,
            expected_str.clone().into_iter().collect(),
        );
        assert_eq!(
            decoded_btree_string,
            expected_string.clone().into_iter().collect(),
        );
    }

    #[test]
    fn test_tuples() {
        let mut tuple_contents = BytesMut::new();
        append_cell(&mut tuple_contents, &42i32.to_be_bytes());
        append_cell(&mut tuple_contents, "foo".as_bytes());
        append_null(&mut tuple_contents);

        let tuple = make_cell(&tuple_contents);

        let typ = ColumnType::Tuple(vec![ColumnType::Int, ColumnType::Ascii, ColumnType::Uuid]);

        let tup = deserialize::<(i32, &str, Option<Uuid>)>(&typ, &tuple).unwrap();
        assert_eq!(tup, (42, "foo", None));
    }

    fn deserialize<'rows, T>(typ: &'rows ColumnType, byts: &'rows Bytes) -> Result<T, ParseError>
    where
        T: FromCql<'rows>,
    {
        <T as FromCql<'rows>>::type_check(typ)?;
        let mut buf = byts.as_ref();
        let cell = types::read_bytes_opt(&mut buf)?;
        let value = RawValue::new(typ, cell, byts);
        <T as FromCql<'rows>>::deserialize(value)
    }

    fn make_cell(cell: &[u8]) -> Bytes {
        let mut b = BytesMut::new();
        append_cell(&mut b, cell);
        b.freeze()
    }

    fn append_cell(b: &mut impl BufMut, cell: &[u8]) {
        b.put_i32(cell.len() as i32);
        b.put_slice(cell);
    }

    fn append_null(b: &mut impl BufMut) {
        b.put_i32(-1);
    }
}
