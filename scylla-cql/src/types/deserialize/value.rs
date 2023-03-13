use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::{BuildHasher, Hash};
use std::net::IpAddr;

use bytes::Bytes;
use chrono::{Duration, NaiveDate};
use uuid::Uuid;

use crate::frame::frame_errors::ParseError;
use crate::frame::response::result::{deser_cql_value, ColumnType, CqlValue};
use crate::frame::types;
use crate::frame::value::{Counter, CqlDuration, Date, Time, Timestamp};

use super::{BytesSequenceIterator, FixedLengthBytesSequenceIterator, FrameSlice};

// TODO: Comprehensive documentation!

/// Description TODO
pub trait DeserializeCql<'frame> {
    /// Result of the deserialization. Usually, it can be just set to `Self`.
    /// However, sometimes it is useful to have different methods
    /// of deserialization which result in the same type.
    type Target;

    /// Checks whether this type can be deserialized from given CQL type.
    fn type_check(typ: &ColumnType) -> Result<(), ParseError>;

    /// Deserialize from given bytes.
    /// The function may assume that `type_check` was called and it succeeded.
    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError>;
}

impl<'frame> DeserializeCql<'frame> for CqlValue {
    type Target = Self;

    fn type_check(_typ: &ColumnType) -> Result<(), ParseError> {
        // Type checking is done in deserialize
        Ok(())
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        let mut val = ensure_not_null(v)?;
        let cql = deser_cql_value(typ, &mut val)?;
        Ok(cql)
    }
}

impl<'frame, T> DeserializeCql<'frame> for Option<T>
where
    T: DeserializeCql<'frame>,
{
    type Target = Option<T::Target>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        T::type_check(typ)
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        v.map(|_| T::deserialize(typ, v)).transpose()
    }
}

macro_rules! impl_strict_type {
    ($cql_name:literal, $t:ty, $cql_type:pat, $conv:expr $(, $l:lifetime)?) => {
        impl<$($l,)? 'frame> DeserializeCql<'frame> for $t
        where
            $('frame: $l)?
        {
            type Target = Self;

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

            fn deserialize(
                typ: &'frame ColumnType,
                v: Option<FrameSlice<'frame>>,
            ) -> Result<Self::Target, ParseError> {
                $conv(typ, v)
            }
        }
    };
}

// fixed numeric types

macro_rules! impl_fixed_numeric_type {
    ($cql_name:literal, $t:ty, $col_type:pat) => {
        impl_strict_type!(
            $cql_name,
            $t,
            $col_type,
            |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
                const SIZE: usize = std::mem::size_of::<$t>();
                let val = ensure_not_null(v)?;
                let arr = ensure_exact_length::<SIZE>($cql_name, val)?;
                Ok(<$t>::from_be_bytes(arr))
            }
        );
    };
}

impl_strict_type!(
    "boolean",
    bool,
    ColumnType::Boolean,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        let arr = ensure_exact_length::<1>("boolean", val)?;
        Ok(arr[0] != 0x00)
    }
);

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
    ColumnType::Varint,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        Ok(num_bigint::BigInt::from_signed_bytes_be(val))
    }
);

impl_strict_type!(
    "decimal",
    bigdecimal::BigDecimal,
    ColumnType::Decimal,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let mut val = ensure_not_null(v)?;
        let scale = types::read_int(&mut val)? as i64;
        let int_value = num_bigint::BigInt::from_signed_bytes_be(val);
        Ok(bigdecimal::BigDecimal::from((int_value, scale)))
    }
);

// blob

impl_strict_type!(
    "blob",
    &'a [u8],
    ColumnType::Blob,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        Ok(val)
    },
    'a
);
impl_strict_type!(
    "blob",
    Vec<u8>,
    ColumnType::Blob,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        Ok(val.to_vec())
    }
);
impl_strict_type!(
    "blob",
    Bytes,
    ColumnType::Blob,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null_owned(v)?;
        Ok(val)
    }
);

// string
// TODO: Types which accept only ascii or text

macro_rules! impl_string_type {
    ($t:ty, $conv:expr $(, $l:lifetime)?) => {
        impl_strict_type!(
            "ascii or text",
            $t,
            ColumnType::Ascii | ColumnType::Text,
            $conv
            $(, $l)?
        );
    };
}

impl_string_type!(
    &'a str,
    |typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        check_ascii(typ, val)?;
        Ok(std::str::from_utf8(val)?)
    },
    'a
);
impl_string_type!(
    String,
    |typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        check_ascii(typ, val)?;
        Ok(std::str::from_utf8(val)?.to_string())
    }
);

// TODO: Deserialization for string::String<Bytes>

fn check_ascii(typ: &ColumnType, s: &[u8]) -> Result<(), ParseError> {
    if matches!(typ, ColumnType::Ascii) && !s.is_ascii() {
        return Err(ParseError::BadIncomingData(
            "Expected a valid ASCII string".to_string(),
        ));
    }
    Ok(())
}

// counter

impl_strict_type!(
    "counter",
    Counter,
    ColumnType::Counter,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        let arr = ensure_exact_length::<8>("counter", val)?;
        let counter = i64::from_be_bytes(arr);
        Ok(Counter(counter))
    }
);

// date and time types

impl_strict_type!(
    "date",
    Date,
    ColumnType::Date,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        let arr = ensure_exact_length::<4>("date", val)?;
        let days = u32::from_be_bytes(arr);
        Ok(Date(days))
    }
);

impl_strict_type!(
    "date",
    NaiveDate,
    ColumnType::Date,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        let arr = ensure_exact_length::<4>("date", val)?;
        let days = u32::from_be_bytes(arr);
        let days_since_epoch = chrono::Duration::days(days as i64 - (1i64 << 31));
        NaiveDate::from_ymd_opt(1970, 1, 1)
            .unwrap()
            .checked_add_signed(days_since_epoch)
            .ok_or_else(|| {
                ParseError::BadIncomingData(format!(
                    "Value is out of representable range for NaiveDate"
                ))
            })
    }
);

impl_strict_type!(
    "duration",
    CqlDuration,
    ColumnType::Duration,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
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
    "time or timestamp",
    Duration,
    ColumnType::Time | ColumnType::Timestamp,
    |typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        // Delegate parsing to time/timestamp impls
        match typ {
            ColumnType::Time => Time::deserialize(typ, v).map(|t| t.0),
            ColumnType::Timestamp => Timestamp::deserialize(typ, v).map(|t| t.0),
            _ => Err(ParseError::BadIncomingData(format!(
                "Invalid type: expected time or timestamp, got {:?}",
                typ,
            ))),
        }
    }
);

impl_strict_type!(
    "timestamp",
    Timestamp,
    ColumnType::Timestamp,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
        let val = ensure_not_null(v)?;
        let arr = ensure_exact_length::<8>("date", val)?;
        let duration = chrono::Duration::milliseconds(i64::from_be_bytes(arr));
        Ok(Timestamp(duration))
    }
);

impl_strict_type!(
    "time",
    Time,
    ColumnType::Time,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
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
    }
);

// inet

impl_strict_type!(
    "inet",
    IpAddr,
    ColumnType::Inet,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
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
    }
);

// uuid
// TODO: Consider having separate types for timeuuid and uuid

impl_strict_type!(
    "timeuuid or uuid",
    Uuid,
    ColumnType::Uuid | ColumnType::Timeuuid,
    |_typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>| {
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
/// `MaybeEmpty` was added in order to support this quirk. The `DeserializeCql`
/// trait is implemented for each `MaybeEmpty<T>` where `T` is a CQL type that
/// can be empty.
pub enum MaybeEmpty<T> {
    Empty,
    Value(T),
}

/// A marker trait for types that can have an "empty" value in CQL.
pub trait EmptyableValue {}

impl<'frame, T> DeserializeCql<'frame> for MaybeEmpty<T>
where
    T: DeserializeCql<'frame> + EmptyableValue,
{
    type Target = MaybeEmpty<T::Target>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        <T as DeserializeCql<'frame>>::type_check(typ)
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        let val = ensure_not_null(v)?;
        if val.is_empty() {
            Ok(MaybeEmpty::Empty)
        } else {
            let v = <T as DeserializeCql<'frame>>::deserialize(typ, v)?;
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
pub struct SequenceIterator<'frame, T> {
    elem_typ: &'frame ColumnType,
    raw_iter: FixedLengthBytesSequenceIterator<'frame>,
    phantom_data: std::marker::PhantomData<T>,
}

impl<'frame, T> SequenceIterator<'frame, T> {
    pub fn new(elem_typ: &'frame ColumnType, count: usize, slice: FrameSlice<'frame>) -> Self {
        Self {
            elem_typ,
            raw_iter: FixedLengthBytesSequenceIterator::new(count, slice),
            phantom_data: std::marker::PhantomData,
        }
    }
}

impl<'frame, T> DeserializeCql<'frame> for SequenceIterator<'frame, T>
where
    T: DeserializeCql<'frame>,
{
    type Target = Self;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        match typ {
            ColumnType::List(el_t) | ColumnType::Set(el_t) => {
                <T as DeserializeCql<'frame>>::type_check(el_t)
            }
            _ => Err(ParseError::BadIncomingData(format!(
                "Expected list or set, got {:?}",
                typ,
            ))),
        }
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        let v = ensure_not_null_slice(v)?;
        let mut mem = v.as_slice();
        let count = types::read_int_length(&mut mem)?;
        let elem_typ = match typ {
            ColumnType::List(elem_typ) | ColumnType::Set(elem_typ) => elem_typ,
            _ => {
                return Err(ParseError::BadIncomingData(format!(
                    "Expected list or set, got {:?}",
                    typ,
                )))
            }
        };
        Ok(Self::new(
            elem_typ,
            count,
            FrameSlice::new_subslice(mem, v.as_bytes_ref()),
        ))
    }
}

impl<'frame, T> Iterator for SequenceIterator<'frame, T>
where
    T: DeserializeCql<'frame>,
{
    type Item = Result<T::Target, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw = self.raw_iter.next()?;
        Some(raw.and_then(|raw| T::deserialize(self.elem_typ, raw)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.raw_iter.size_hint()
    }
}

// TODO: Can we implement DeserializeCql for every type that can collect from an iter?
// I'm not sure it is possible, there will be conflicts with MapIterator
// and collections of pairs

impl<'frame, T> DeserializeCql<'frame> for Vec<T>
where
    T: DeserializeCql<'frame>,
{
    type Target = Vec<T::Target>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        SequenceIterator::<'frame, T>::type_check(typ)
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        SequenceIterator::<'frame, T>::deserialize(typ, v)?.collect()
    }
}

impl<'frame, T> DeserializeCql<'frame> for BTreeSet<T>
where
    T: DeserializeCql<'frame>,
    T::Target: Ord,
{
    type Target = BTreeSet<T::Target>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        SequenceIterator::<'frame, T>::type_check(typ)
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        SequenceIterator::<'frame, T>::deserialize(typ, v)?.collect()
    }
}

impl<'frame, T, S> DeserializeCql<'frame> for HashSet<T, S>
where
    T: DeserializeCql<'frame>,
    T::Target: Eq + Hash,
    S: BuildHasher + Default + 'frame,
{
    type Target = HashSet<T::Target>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        SequenceIterator::<'frame, T>::type_check(typ)
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        SequenceIterator::<'frame, T>::deserialize(typ, v)?.collect()
    }
}

pub struct MapIterator<'frame, K, V> {
    k_typ: &'frame ColumnType,
    v_typ: &'frame ColumnType,
    raw_iter: FixedLengthBytesSequenceIterator<'frame>,
    phantom_data_k: std::marker::PhantomData<K>,
    phantom_data_v: std::marker::PhantomData<V>,
}

impl<'frame, K, V> DeserializeCql<'frame> for MapIterator<'frame, K, V>
where
    K: DeserializeCql<'frame>,
    V: DeserializeCql<'frame>,
{
    type Target = MapIterator<'frame, K, V>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        match typ {
            ColumnType::Map(k_t, v_t) => {
                <K as DeserializeCql<'frame>>::type_check(k_t)?;
                <V as DeserializeCql<'frame>>::type_check(v_t)?;
                Ok(())
            }
            _ => Err(ParseError::BadIncomingData(format!(
                "Expected map, got {:?}",
                typ,
            ))),
        }
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        let v = ensure_not_null_slice(v)?;
        let mut mem = v.as_slice();
        let count = types::read_int_length(&mut mem)?;
        let (k_typ, v_typ) = match typ {
            ColumnType::Map(k_t, v_t) => (k_t, v_t),
            _ => {
                return Err(ParseError::BadIncomingData(format!(
                    "Expected map, got {:?}",
                    typ,
                )))
            }
        };
        Ok(Self {
            k_typ,
            v_typ,
            raw_iter: FixedLengthBytesSequenceIterator::new(
                2 * count,
                FrameSlice::new_subslice(mem, v.as_bytes_ref()),
            ),
            phantom_data_k: std::marker::PhantomData,
            phantom_data_v: std::marker::PhantomData,
        })
    }
}

impl<'frame, K, V> Iterator for MapIterator<'frame, K, V>
where
    K: DeserializeCql<'frame>,
    V: DeserializeCql<'frame>,
{
    type Item = Result<(K::Target, V::Target), ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_k = match self.raw_iter.next() {
            Some(Ok(raw_k)) => raw_k,
            Some(Err(err)) => return Some(Err(err)),
            None => return None,
        };
        let raw_v = match self.raw_iter.next() {
            Some(Ok(raw_v)) => raw_v,
            Some(Err(err)) => return Some(Err(err)),
            None => return None,
        };
        let do_next = || -> Result<(K::Target, V::Target), ParseError> {
            let k = K::deserialize(self.k_typ, raw_k)?;
            let v = V::deserialize(self.v_typ, raw_v)?;
            Ok((k, v))
        };
        do_next().map(Some).transpose()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.raw_iter.size_hint()
    }
}

impl<'frame, K, V> DeserializeCql<'frame> for BTreeMap<K, V>
where
    K: DeserializeCql<'frame>,
    K::Target: Ord,
    V: DeserializeCql<'frame>,
{
    type Target = BTreeMap<K::Target, V::Target>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        MapIterator::<'frame, K, V>::type_check(typ)
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        MapIterator::<'frame, K, V>::deserialize(typ, v)?.collect()
    }
}

impl<'frame, K, V, S> DeserializeCql<'frame> for HashMap<K, V, S>
where
    K: DeserializeCql<'frame>,
    K::Target: Eq + Hash,
    V: DeserializeCql<'frame>,
    S: BuildHasher + Default + 'frame,
{
    type Target = HashMap<K::Target, V::Target, S>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        MapIterator::<'frame, K, V>::type_check(typ)
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        MapIterator::<'frame, K, V>::deserialize(typ, v)?.collect()
    }
}

// tuples

// Implements tuple deserialization.
// The generated impl expects that the serialized data will contain at least
// the given amount of values.
// TODO: Offer more flexible, compatible options
// TODO: Add more context to errors
macro_rules! impl_tuple {
    ($($Ti:ident),*; $($idx:literal),*; $($idf:ident),*) => {
        impl<'frame, $($Ti),*> DeserializeCql<'frame> for ($($Ti,)*)
        where
            $($Ti: DeserializeCql<'frame>),*
        {
            type Target = ($($Ti::Target,)*);

            fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
                const TUPLE_LEN: usize = [0, $($idx),*].len() - 1;
                let [$($idf),*] = ensure_tuple_type::<TUPLE_LEN>(typ)?;
                $(
                    <$Ti>::type_check($idf)?;
                )*
                Ok(())
            }

            fn deserialize(typ: &'frame ColumnType, v: Option<FrameSlice<'frame>>) -> Result<Self::Target, ParseError> {
                const TUPLE_LEN: usize = [0, $($idx),*].len() - 1;
                let [$($idf),*] = ensure_tuple_type::<TUPLE_LEN>(typ)?;

                // Ignore the warning for the zero-sized tuple
                #[allow(unused)]
                let mut v = ensure_not_null_slice(v)?;
                let ret = (
                    $(
                        <$Ti>::deserialize($idf, v.read_cql_bytes()?)?,
                    )*
                );
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

// udts

/// An iterator over fields of a User Defined Type.
///
/// # Note
///
/// A serialized UDT will generally have one value for each field, but it is
/// allowed to have less. This iterator differentiates null values
/// from non-existent values in the following way:
///
/// - `None` - missing from the serialized form
/// - `Some(None)` - present, but null
/// - `Some(Some(...))` - non-null, present value
pub struct UdtIterator<'frame> {
    fields: &'frame [(String, ColumnType)],
    raw_iter: BytesSequenceIterator<'frame>,
}

impl<'frame> UdtIterator<'frame> {
    #[inline]
    pub fn new(fields: &'frame [(String, ColumnType)], slice: FrameSlice<'frame>) -> Self {
        Self {
            fields,
            raw_iter: BytesSequenceIterator::new(slice),
        }
    }

    #[inline]
    pub fn fields(&self) -> &'frame [(String, ColumnType)] {
        self.fields
    }
}

impl<'frame> DeserializeCql<'frame> for UdtIterator<'frame> {
    type Target = UdtIterator<'frame>;

    fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
        match typ {
            ColumnType::UserDefinedType { .. } => Ok(()),
            _ => Err(ParseError::BadIncomingData(format!(
                "Expected a user defined type, got {:?}",
                typ,
            ))),
        }
    }

    fn deserialize(
        typ: &'frame ColumnType,
        v: Option<FrameSlice<'frame>>,
    ) -> Result<Self::Target, ParseError> {
        let v = ensure_not_null_slice(v)?;
        let mem = v.as_slice();
        let fields = match typ {
            ColumnType::UserDefinedType { field_types, .. } => field_types.as_ref(),
            _ => {
                return Err(ParseError::BadIncomingData(format!(
                    "Expected a user defined type, got {:?}",
                    typ,
                )))
            }
        };
        Ok(Self::new(
            fields,
            FrameSlice::new_subslice(mem, v.as_bytes_ref()),
        ))
    }
}

impl<'frame> Iterator for UdtIterator<'frame> {
    type Item = Result<
        (
            &'frame (String, ColumnType),
            Option<Option<FrameSlice<'frame>>>,
        ),
        ParseError,
    >;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO: Should we fail when there are too many fields?
        let (head, fields) = self.fields.split_first()?;
        self.fields = fields;
        let raw = match self.raw_iter.next() {
            // The field is there and it was parsed correctly
            Some(Ok(raw)) => Some(raw),

            // There were some bytes but they didn't parse as correct field value
            Some(Err(err)) => return Some(Err(err)),

            // The field is just missing from the serialized form
            None => None,
        };
        Some(Ok((head, raw)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.raw_iter.size_hint()
    }
}

// Utilities

fn ensure_not_null<'frame>(v: Option<FrameSlice<'frame>>) -> Result<&[u8], ParseError> {
    match v {
        Some(v) => Ok(v.as_slice()),
        None => Err(ParseError::BadIncomingData(
            "Expected a non-null value".to_string(),
        )),
    }
}

fn ensure_not_null_owned<'frame>(v: Option<FrameSlice<'frame>>) -> Result<Bytes, ParseError> {
    match v {
        Some(v) => Ok(v.to_bytes()),
        None => Err(ParseError::BadIncomingData(
            "Expected a non-null value".to_string(),
        )),
    }
}

fn ensure_not_null_slice<'frame>(
    v: Option<FrameSlice<'frame>>,
) -> Result<FrameSlice<'frame>, ParseError> {
    match v {
        Some(v) => Ok(v),
        None => Err(ParseError::BadIncomingData(
            "Expected a non-null value".to_string(),
        )),
    }
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

fn ensure_tuple_type<const SIZE: usize>(
    typ: &ColumnType,
) -> Result<&[ColumnType; SIZE], ParseError> {
    let fail = || {
        ParseError::BadIncomingData(format!(
            "Expected tuple of size {}, but got {:?}",
            SIZE, typ,
        ))
    };
    if let ColumnType::Tuple(typs_v) = typ {
        typs_v.as_slice().try_into().map_err(|_| fail())
    } else {
        Err(fail())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
    use std::fmt::Debug;
    use std::marker::PhantomData;
    use std::net::{IpAddr, Ipv6Addr};

    use bigdecimal::BigDecimal;
    use bytes::{BufMut, Bytes, BytesMut};
    use chrono::{Duration, NaiveDate};
    use num_bigint::BigInt;
    use scylla_macros::DeserializeCql;
    use uuid::Uuid;

    use crate::frame::response::cql_to_rust::FromCqlVal;
    use crate::frame::response::result::{ColumnType, CqlValue};
    use crate::frame::types;
    use crate::frame::value::{CqlDuration, Value};
    use crate::frame::value::{Date, Time, Timestamp};
    use crate::frame::{
        frame_errors::ParseError, response::result::deser_cql_value, value::Counter,
    };
    use crate::types::deserialize::FrameSlice;

    use super::{DeserializeCql, MapIterator, SequenceIterator};

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
        const ASCII_TEXT: &str = "The quick brown fox jumps over the lazy dog";

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

        // TODO: Deserialization of tuples with less elements?
    }

    #[test]
    fn test_udt_loose_ordering() {
        #[derive(DeserializeCql, PartialEq, Eq, Debug)]
        #[scylla(crate = "crate")]
        struct Udt<'a> {
            a: &'a str,
            #[scylla(skip)]
            x: String,
            #[scylla(default_when_missing)]
            b: Option<i32>,
        }

        // Columns in correct same order
        let mut udt_contents = BytesMut::new();
        append_cell(&mut udt_contents, "The quick brown fox".as_bytes());
        append_cell(&mut udt_contents, &42i32.to_be_bytes());
        let udt = make_cell(&udt_contents);
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![
                ("a".to_owned(), ColumnType::Text),
                ("b".to_owned(), ColumnType::Int),
            ],
        };

        let udt = deserialize::<Udt<'_>>(&typ, &udt).unwrap();
        assert_eq!(
            udt,
            Udt {
                a: "The quick brown fox",
                x: String::new(),
                b: Some(42),
            }
        );

        // Columns switched - should still work
        let mut udt_contents = BytesMut::new();
        append_cell(&mut udt_contents, &42i32.to_be_bytes());
        append_cell(&mut udt_contents, "The quick brown fox".as_bytes());
        let udt = make_cell(&udt_contents);
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![
                ("b".to_owned(), ColumnType::Int),
                ("a".to_owned(), ColumnType::Text),
            ],
        };

        let udt = deserialize::<Udt<'_>>(&typ, &udt).unwrap();
        assert_eq!(
            udt,
            Udt {
                a: "The quick brown fox",
                x: String::new(),
                b: Some(42),
            }
        );

        // Only column 'a' is present
        let mut udt_contents = BytesMut::new();
        append_cell(&mut udt_contents, "The quick brown fox".as_bytes());
        let udt = make_cell(&udt_contents);
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![("a".to_owned(), ColumnType::Text)],
        };

        let udt = deserialize::<Udt<'_>>(&typ, &udt).unwrap();
        assert_eq!(
            udt,
            Udt {
                a: "The quick brown fox",
                x: String::new(),
                b: None,
            }
        );

        // Wrong column type
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![("a".to_owned(), ColumnType::Int)],
        };
        Udt::type_check(&typ).unwrap_err();

        // Missing required column
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![("b".to_owned(), ColumnType::Int)],
        };
        Udt::type_check(&typ).unwrap_err();
    }

    #[test]
    fn test_udt_strict_ordering() {
        #[derive(DeserializeCql, PartialEq, Eq, Debug)]
        #[scylla(crate = "crate", enforce_order)]
        struct Udt<'a> {
            a: &'a str,
            #[scylla(skip)]
            x: String,
            b: Option<i32>,
        }

        // Columns in correct same order
        let mut udt_contents = BytesMut::new();
        append_cell(&mut udt_contents, "The quick brown fox".as_bytes());
        append_cell(&mut udt_contents, &42i32.to_be_bytes());
        let udt = make_cell(&udt_contents);
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![
                ("a".to_owned(), ColumnType::Text),
                ("b".to_owned(), ColumnType::Int),
            ],
        };

        let udt = deserialize::<Udt<'_>>(&typ, &udt).unwrap();
        assert_eq!(
            udt,
            Udt {
                a: "The quick brown fox",
                x: String::new(),
                b: Some(42),
            }
        );

        // Columns switched - will not work
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![
                ("b".to_owned(), ColumnType::Int),
                ("a".to_owned(), ColumnType::Text),
            ],
        };
        Udt::type_check(&typ).unwrap_err();

        // Wrong column type
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![
                ("a".to_owned(), ColumnType::Int),
                ("b".to_owned(), ColumnType::Int),
            ],
        };
        Udt::type_check(&typ).unwrap_err();

        // Missing required column
        let typ = ColumnType::UserDefinedType {
            type_name: "udt".to_owned(),
            keyspace: "ks".to_owned(),
            field_types: vec![("b".to_owned(), ColumnType::Int)],
        };
        Udt::type_check(&typ).unwrap_err();
    }

    #[test]
    fn test_custom_type_parser() {
        #[derive(Default)]
        struct SwappedPair<A, B> {
            _phantom_a: PhantomData<A>,
            _phantom_b: PhantomData<B>,
        }
        impl<'frame, A, B> DeserializeCql<'frame> for SwappedPair<A, B>
        where
            A: DeserializeCql<'frame>,
            B: DeserializeCql<'frame>,
        {
            type Target = (B::Target, A::Target);

            fn type_check(typ: &ColumnType) -> Result<(), ParseError> {
                <(B, A) as DeserializeCql<'frame>>::type_check(typ)
            }

            fn deserialize(
                typ: &'frame ColumnType,
                v: Option<FrameSlice<'frame>>,
            ) -> Result<Self::Target, ParseError> {
                <(B, A) as DeserializeCql<'frame>>::deserialize(typ, v)
            }
        }

        let mut tuple_contents = BytesMut::new();
        append_cell(&mut tuple_contents, "foo".as_bytes());
        append_cell(&mut tuple_contents, &42i32.to_be_bytes());
        let tuple = make_cell(&tuple_contents);

        let typ = ColumnType::Tuple(vec![ColumnType::Ascii, ColumnType::Int]);

        let tup = deserialize::<SwappedPair<i32, &str>>(&typ, &tuple).unwrap();
        assert_eq!(tup, ("foo", 42));
    }

    #[test]
    fn test_from_cql_value_compatibility() {
        // This test should have a sub-case for each type
        // that implements FromCqlValue

        // Types covered by impl_from_cql_value_from_method

        // fixed size integers
        for i in 0..7 {
            let v: i8 = 1 << i;
            compat_check::<i8>(&ColumnType::TinyInt, make_cell(&v.to_be_bytes()));
            compat_check::<i8>(&ColumnType::TinyInt, make_cell(&(-v).to_be_bytes()));
        }
        for i in 0..15 {
            let v: i16 = 1 << i;
            compat_check::<i16>(&ColumnType::SmallInt, make_cell(&v.to_be_bytes()));
            compat_check::<i16>(&ColumnType::SmallInt, make_cell(&(-v).to_be_bytes()));
        }
        for i in 0..31 {
            let v: i32 = 1 << i;
            compat_check::<i32>(&ColumnType::Int, make_cell(&v.to_be_bytes()));
            compat_check::<i32>(&ColumnType::Int, make_cell(&(-v).to_be_bytes()));
        }
        for i in 0..63 {
            let v: i64 = 1 << i;
            compat_check::<i64>(&ColumnType::BigInt, make_cell(&v.to_be_bytes()));
            compat_check::<i64>(&ColumnType::BigInt, make_cell(&(-v).to_be_bytes()));
        }

        // TODO: AFAIK counters can be deserialized both from Counter column type
        // and BigInt column type... which is stupid IMO
        for i in 0..63 {
            let v: i64 = 1 << i;
            compat_check::<Counter>(&ColumnType::Counter, make_cell(&v.to_be_bytes()));
        }

        // bool
        compat_check::<bool>(&ColumnType::Boolean, make_cell(&[0]));
        compat_check::<bool>(&ColumnType::Boolean, make_cell(&[1]));

        // fixed size floating point types
        compat_check::<f32>(&ColumnType::Float, make_cell(&123f32.to_be_bytes()));
        compat_check::<f32>(&ColumnType::Float, make_cell(&(-123f32).to_be_bytes()));
        compat_check::<f64>(&ColumnType::Double, make_cell(&123f64.to_be_bytes()));
        compat_check::<f64>(&ColumnType::Double, make_cell(&(-123f64).to_be_bytes()));

        const PI_STR: &[u8] = b"3.1415926535897932384626433832795028841971693993751058209749445923";

        // big integers
        let num1 = PI_STR[2..].to_vec();
        let num2 = vec!['-' as u8]
            .into_iter()
            .chain(PI_STR[2..].iter().copied())
            .collect::<Vec<_>>();
        let num3 = b"0".to_vec();

        let num1 = BigInt::parse_bytes(&num1, 10).unwrap();
        let num2 = BigInt::parse_bytes(&num2, 10).unwrap();
        let num3 = BigInt::parse_bytes(&num3, 10).unwrap();
        compat_check::<BigInt>(&ColumnType::Varint, serialize_cell(&num1));
        compat_check::<BigInt>(&ColumnType::Varint, serialize_cell(&num2));
        compat_check::<BigInt>(&ColumnType::Varint, serialize_cell(&num3));

        // big decimals
        let num1 = PI_STR.to_vec();
        let num2 = vec!['-' as u8]
            .into_iter()
            .chain(PI_STR.iter().copied())
            .collect::<Vec<_>>();
        let num3 = b"0.0".to_vec();

        let num1 = BigDecimal::parse_bytes(&num1, 10).unwrap();
        let num2 = BigDecimal::parse_bytes(&num2, 10).unwrap();
        let num3 = BigDecimal::parse_bytes(&num3, 10).unwrap();
        compat_check::<BigDecimal>(&ColumnType::Decimal, serialize_cell(&num1));
        compat_check::<BigDecimal>(&ColumnType::Decimal, serialize_cell(&num2));
        compat_check::<BigDecimal>(&ColumnType::Decimal, serialize_cell(&num3));

        // date and time
        let date1 = (2u32.pow(31)).to_be_bytes();
        let date2 = (2u32.pow(31) - 30).to_be_bytes();
        let date3 = (2u32.pow(31) + 30).to_be_bytes();
        compat_check::<NaiveDate>(&ColumnType::Date, make_cell(&date1));
        compat_check::<NaiveDate>(&ColumnType::Date, make_cell(&date2));
        compat_check::<NaiveDate>(&ColumnType::Date, make_cell(&date3));

        let timestamp1 = Duration::milliseconds(123);
        let timestamp2 = Duration::seconds(123);
        let timestamp3 = Duration::hours(18);
        // Duration type is relevant for both `time` and `timestamp` CQL types
        compat_check::<Duration>(&ColumnType::Time, serialize_cell(&Time(timestamp1)));
        compat_check::<Duration>(&ColumnType::Time, serialize_cell(&Time(timestamp2)));
        compat_check::<Duration>(&ColumnType::Time, serialize_cell(&Time(timestamp3)));
        compat_check::<Duration>(
            &ColumnType::Timestamp,
            serialize_cell(&Timestamp(timestamp1)),
        );
        compat_check::<Duration>(
            &ColumnType::Timestamp,
            serialize_cell(&Timestamp(timestamp2)),
        );
        compat_check::<Duration>(
            &ColumnType::Timestamp,
            serialize_cell(&Timestamp(timestamp3)),
        );

        // duration
        let duration1 = CqlDuration {
            days: 123,
            months: 456,
            nanoseconds: 789,
        };
        let duration2 = CqlDuration {
            days: 987,
            months: 654,
            nanoseconds: 321,
        };
        compat_check::<CqlDuration>(&ColumnType::Duration, serialize_cell(&duration1));
        compat_check::<CqlDuration>(&ColumnType::Duration, serialize_cell(&duration2));

        // text types
        for typ in &[ColumnType::Ascii, ColumnType::Text] {
            compat_check::<String>(typ, make_cell("".as_bytes()));
            compat_check::<String>(typ, make_cell("foo".as_bytes()));
            compat_check::<String>(typ, make_cell("superfragilisticexpialidocious".as_bytes()));
        }

        // blob
        compat_check::<Vec<u8>>(&ColumnType::Blob, make_cell(&[]));
        compat_check::<Vec<u8>>(&ColumnType::Blob, make_cell(&[1, 9, 2, 8, 3, 7, 4, 6, 5]));

        let ipv4 = IpAddr::from([127u8, 0, 0, 1]);
        let ipv6: IpAddr = Ipv6Addr::LOCALHOST.into();
        compat_check::<IpAddr>(&ColumnType::Inet, make_ip_address(ipv4));
        compat_check::<IpAddr>(&ColumnType::Inet, make_ip_address(ipv6));

        // TODO: Finish the rest
        // As a finishing touch
        // For now, it's more important to adapt the rest of the codebase

        // Post

        compat_check::<Date>(&ColumnType::Date, make_cell(&date1));
        compat_check::<Date>(&ColumnType::Date, make_cell(&date2));
        compat_check::<Date>(&ColumnType::Date, make_cell(&date3));
    }

    // Checks that both new and old serialization framework
    // produces the same results in this case
    fn compat_check<T>(typ: &ColumnType, raw: Bytes)
    where
        T: for<'f> DeserializeCql<'f, Target = T>,
        T: FromCqlVal<CqlValue>,
        T: Debug + PartialEq,
    {
        let mut slice = raw.as_ref();
        let mut cell = types::read_bytes_opt(&mut slice).unwrap().unwrap();
        let old = T::from_cql(deser_cql_value(typ, &mut cell).unwrap()).unwrap();
        let new = deserialize::<T>(typ, &raw).unwrap();
        assert_eq!(old, new);
    }

    fn deserialize<'frame, T>(
        typ: &'frame ColumnType,
        byts: &'frame Bytes,
    ) -> Result<T::Target, ParseError>
    where
        T: DeserializeCql<'frame>,
    {
        <T as DeserializeCql<'frame>>::type_check(typ)?;
        let mut buf = byts.as_ref();
        let cell = types::read_bytes_opt(&mut buf)?;
        let value = cell.map(|cell| FrameSlice::new_subslice(cell, byts));
        <T as DeserializeCql<'frame>>::deserialize(typ, value)
    }

    fn make_cell(cell: &[u8]) -> Bytes {
        let mut b = BytesMut::new();
        append_cell(&mut b, cell);
        b.freeze()
    }

    fn serialize_cell(value: &impl Value) -> Bytes {
        let mut v = Vec::new();
        value.serialize(&mut v).unwrap();
        v.into()
    }

    fn make_ip_address(ip: IpAddr) -> Bytes {
        match ip {
            IpAddr::V4(v4) => make_cell(&v4.octets()),
            IpAddr::V6(v6) => make_cell(&v6.octets()),
        }
    }

    fn append_cell(b: &mut impl BufMut, cell: &[u8]) {
        b.put_i32(cell.len() as i32);
        b.put_slice(cell);
    }

    fn append_null(b: &mut impl BufMut) {
        b.put_i32(-1);
    }

    // TODO: Tests for iterators
}