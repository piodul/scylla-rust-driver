use std::borrow::Cow;
use std::collections::{BTreeMap, HashSet};
use std::fmt::Display;
use std::hash::BuildHasher;
use std::{collections::HashMap, sync::Arc};

use bytes::BufMut;
use thiserror::Error;

use crate::frame::frame_errors::ParseError;
use crate::frame::response::result::ColumnType;
use crate::frame::response::result::PreparedMetadata;
use crate::frame::types;
use crate::frame::value::SerializeValuesError;
use crate::frame::value::{LegacySerializedValues, ValueList};
use crate::frame::{response::result::ColumnSpec, types::RawValue};

use super::value::SerializeCql;
use super::{CellWriter, RowWriter, SerializationError};

/// Contains information needed to serialize a row.
pub struct RowSerializationContext<'a> {
    pub(crate) columns: &'a [ColumnSpec],
}

impl<'a> RowSerializationContext<'a> {
    #[inline]
    pub fn from_prepared(prepared: &'a PreparedMetadata) -> Self {
        Self {
            columns: prepared.col_specs.as_slice(),
        }
    }

    #[inline]
    pub const fn empty() -> Self {
        Self { columns: &[] }
    }

    /// Returns column/bind marker specifications for given query.
    #[inline]
    pub fn columns(&self) -> &'a [ColumnSpec] {
        self.columns
    }

    /// Looks up and returns a column/bind marker by name.
    // TODO: change RowSerializationContext to make this faster
    #[inline]
    pub fn column_by_name(&self, target: &str) -> Option<&ColumnSpec> {
        self.columns.iter().find(|&c| c.name == target)
    }
}

pub trait SerializeRow {
    /// Serializes the row according to the information in the given context.
    fn serialize(
        &self,
        ctx: &RowSerializationContext<'_>,
        writer: &mut RowWriter,
    ) -> Result<(), SerializationError>;

    fn is_empty(&self) -> bool;
}

macro_rules! fallback_impl_contents {
    () => {
        fn serialize(
            &self,
            ctx: &RowSerializationContext<'_>,
            writer: &mut RowWriter,
        ) -> Result<(), SerializationError> {
            serialize_legacy_row(self, ctx, writer)
        }
        #[inline]
        fn is_empty(&self) -> bool {
            LegacySerializedValues::is_empty(self)
        }
    };
}

macro_rules! impl_serialize_row_for_unit {
    () => {
        fn serialize(
            &self,
            ctx: &RowSerializationContext<'_>,
            _writer: &mut RowWriter,
        ) -> Result<(), SerializationError> {
            if !ctx.columns().is_empty() {
                return Err(mk_typck_err::<Self>(
                    BuiltinTypeCheckErrorKind::WrongColumnCount {
                        actual: 0,
                        asked_for: ctx.columns().len(),
                    },
                ));
            }
            // Row is empty - do nothing
            Ok(())
        }

        #[inline]
        fn is_empty(&self) -> bool {
            true
        }
    };
}

impl SerializeRow for () {
    impl_serialize_row_for_unit!();
}

impl SerializeRow for [u8; 0] {
    impl_serialize_row_for_unit!();
}

macro_rules! impl_serialize_row_for_slice {
    () => {
        fn serialize(
            &self,
            ctx: &RowSerializationContext<'_>,
            writer: &mut RowWriter,
        ) -> Result<(), SerializationError> {
            if ctx.columns().len() != self.len() {
                return Err(mk_typck_err::<Self>(
                    BuiltinTypeCheckErrorKind::WrongColumnCount {
                        actual: self.len(),
                        asked_for: ctx.columns().len(),
                    },
                ));
            }
            for (col, val) in ctx.columns().iter().zip(self.iter()) {
                <T as SerializeCql>::serialize(val, &col.typ, writer.make_cell_writer()).map_err(
                    |err| {
                        mk_ser_err::<Self>(
                            BuiltinSerializationErrorKind::ColumnSerializationFailed {
                                name: col.name.clone(),
                                err,
                            },
                        )
                    },
                )?;
            }
            Ok(())
        }

        #[inline]
        fn is_empty(&self) -> bool {
            <[T]>::is_empty(self.as_ref())
        }
    };
}

impl<'a, T: SerializeCql + 'a> SerializeRow for &'a [T] {
    impl_serialize_row_for_slice!();
}

impl<T: SerializeCql> SerializeRow for Vec<T> {
    impl_serialize_row_for_slice!();
}

macro_rules! impl_serialize_row_for_map {
    () => {
        fn serialize(
            &self,
            ctx: &RowSerializationContext<'_>,
            writer: &mut RowWriter,
        ) -> Result<(), SerializationError> {
            // Unfortunately, column names aren't guaranteed to be unique.
            // We need to track not-yet-used columns in order to see
            // whether some values were not used at the end, and report an error.
            let mut unused_columns: HashSet<&str> = self.keys().map(|k| k.as_ref()).collect();

            for col in ctx.columns.iter() {
                match self.get(col.name.as_str()) {
                    None => {
                        return Err(mk_typck_err::<Self>(
                            BuiltinTypeCheckErrorKind::MissingValueForColumn {
                                name: col.name.clone(),
                            },
                        ))
                    }
                    Some(v) => {
                        <T as SerializeCql>::serialize(v, &col.typ, writer.make_cell_writer())
                            .map_err(|err| {
                                mk_ser_err::<Self>(
                                    BuiltinSerializationErrorKind::ColumnSerializationFailed {
                                        name: col.name.clone(),
                                        err,
                                    },
                                )
                            })?;
                        let _ = unused_columns.remove(col.name.as_str());
                    }
                }
            }

            if !unused_columns.is_empty() {
                // Report the lexicographically first value for deterministic error messages
                let name = unused_columns.iter().min().unwrap();
                return Err(mk_typck_err::<Self>(
                    BuiltinTypeCheckErrorKind::ColumnMissingForValue {
                        name: name.to_string(),
                    },
                ));
            }

            Ok(())
        }

        #[inline]
        fn is_empty(&self) -> bool {
            Self::is_empty(self)
        }
    };
}

impl<T: SerializeCql> SerializeRow for BTreeMap<String, T> {
    impl_serialize_row_for_map!();
}

impl<T: SerializeCql> SerializeRow for BTreeMap<&str, T> {
    impl_serialize_row_for_map!();
}

impl<T: SerializeCql, S: BuildHasher> SerializeRow for HashMap<String, T, S> {
    impl_serialize_row_for_map!();
}

impl<T: SerializeCql, S: BuildHasher> SerializeRow for HashMap<&str, T, S> {
    impl_serialize_row_for_map!();
}

impl<T: SerializeRow + ?Sized> SerializeRow for &T {
    fn serialize(
        &self,
        ctx: &RowSerializationContext<'_>,
        writer: &mut RowWriter,
    ) -> Result<(), SerializationError> {
        <T as SerializeRow>::serialize(self, ctx, writer)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        <T as SerializeRow>::is_empty(self)
    }
}

impl SerializeRow for LegacySerializedValues {
    fallback_impl_contents!();
}

impl<'b> SerializeRow for Cow<'b, LegacySerializedValues> {
    fallback_impl_contents!();
}

macro_rules! impl_tuple {
    (
        $($typs:ident),*;
        $($fidents:ident),*;
        $($tidents:ident),*;
        $length:expr
    ) => {
        impl<$($typs: SerializeCql),*> SerializeRow for ($($typs,)*) {
            fn serialize(
                &self,
                ctx: &RowSerializationContext<'_>,
                writer: &mut RowWriter,
            ) -> Result<(), SerializationError> {
                let ($($tidents,)*) = match ctx.columns() {
                    [$($tidents),*] => ($($tidents,)*),
                    _ => return Err(mk_typck_err::<Self>(
                        BuiltinTypeCheckErrorKind::WrongColumnCount {
                            actual: $length,
                            asked_for: ctx.columns().len(),
                        },
                    )),
                };
                let ($($fidents,)*) = self;
                $(
                    <$typs as SerializeCql>::serialize($fidents, &$tidents.typ, writer.make_cell_writer()).map_err(|err| {
                        mk_ser_err::<Self>(BuiltinSerializationErrorKind::ColumnSerializationFailed {
                            name: $tidents.name.clone(),
                            err,
                        })
                    })?;
                )*
                Ok(())
            }

            #[inline]
            fn is_empty(&self) -> bool {
                $length == 0
            }
        }
    };
}

macro_rules! impl_tuples {
    (;;;$length:expr) => {};
    (
        $typ:ident$(, $($typs:ident),*)?;
        $fident:ident$(, $($fidents:ident),*)?;
        $tident:ident$(, $($tidents:ident),*)?;
        $length:expr
    ) => {
        impl_tuples!(
            $($($typs),*)?;
            $($($fidents),*)?;
            $($($tidents),*)?;
            $length - 1
        );
        impl_tuple!(
            $typ$(, $($typs),*)?;
            $fident$(, $($fidents),*)?;
            $tident$(, $($tidents),*)?;
            $length
        );
    };
}

impl_tuples!(
    T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15;
    f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15;
    t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15;
    16
);

/// Implements the [`SerializeRow`] trait for a type, provided that the type
/// already implements the legacy
/// [`ValueList`](crate::frame::value::ValueList) trait.
///
/// # Note
///
/// The translation from one trait to another encounters a performance penalty
/// and does not utilize the stronger guarantees of `SerializeRow`. Before
/// resorting to this macro, you should consider other options instead:
///
/// - If the impl was generated using the `ValueList` procedural macro, you
///   should switch to the `SerializeRow` procedural macro. *The new macro
///   behaves differently by default, so please read its documentation first!*
/// - If the impl was written by hand, it is still preferable to rewrite it
///   manually. You have an opportunity to make your serialization logic
///   type-safe and potentially improve performance.
///
/// Basically, you should consider using the macro if you have a hand-written
/// impl and the moment it is not easy/not desirable to rewrite it.
///
/// # Example
///
/// ```rust
/// # use std::borrow::Cow;
/// # use scylla_cql::frame::value::{Value, ValueList, SerializedResult, LegacySerializedValues};
/// # use scylla_cql::impl_serialize_row_via_value_list;
/// struct NoGenerics {}
/// impl ValueList for NoGenerics {
///     fn serialized(&self) -> SerializedResult<'_> {
///         ().serialized()
///     }
/// }
/// impl_serialize_row_via_value_list!(NoGenerics);
///
/// // Generic types are also supported. You must specify the bounds if the
/// // struct/enum contains any.
/// struct WithGenerics<T, U: Clone>(T, U);
/// impl<T: Value, U: Clone + Value> ValueList for WithGenerics<T, U> {
///     fn serialized(&self) -> SerializedResult<'_> {
///         let mut values = LegacySerializedValues::new();
///         values.add_value(&self.0);
///         values.add_value(&self.1.clone());
///         Ok(Cow::Owned(values))
///     }
/// }
/// impl_serialize_row_via_value_list!(WithGenerics<T, U: Clone>);
/// ```
#[macro_export]
macro_rules! impl_serialize_row_via_value_list {
    ($t:ident$(<$($targ:tt $(: $tbound:tt)?),*>)?) => {
        impl $(<$($targ $(: $tbound)?),*>)? $crate::types::serialize::row::SerializeRow
        for $t$(<$($targ),*>)?
        where
            Self: $crate::frame::value::ValueList,
        {
            fn serialize(
                &self,
                ctx: &$crate::types::serialize::row::RowSerializationContext<'_>,
                writer: &mut $crate::types::serialize::writers::RowWriter,
            ) -> ::std::result::Result<(), $crate::types::serialize::SerializationError> {
                $crate::types::serialize::row::serialize_legacy_row(self, ctx, writer)
            }

            #[inline]
            fn is_empty(&self) -> bool {
                match $crate::frame::value::ValueList::serialized(self) {
                    Ok(s) => s.is_empty(),
                    Err(e) => false
                }
            }
        }
    };
}

/// Serializes an object implementing [`ValueList`] by using the [`RowWriter`]
/// interface.
///
/// The function first serializes the value with [`ValueList::serialized`], then
/// parses the result and serializes it again with given `RowWriter`. In case
/// or serialized values with names, they are converted to serialized values
/// without names, based on the information about the bind markers provided
/// in the [`RowSerializationContext`].
///
/// It is a lazy and inefficient way to implement `RowWriter` via an existing
/// `ValueList` impl.
///
/// Returns an error if `ValueList::serialized` call failed or, in case of
/// named serialized values, some bind markers couldn't be matched to a
/// named value.
///
/// See [`impl_serialize_row_via_value_list`] which generates a boilerplate
/// [`SerializeRow`] implementation that uses this function.
pub fn serialize_legacy_row<T: ValueList>(
    r: &T,
    ctx: &RowSerializationContext<'_>,
    writer: &mut RowWriter,
) -> Result<(), SerializationError> {
    let serialized =
        <T as ValueList>::serialized(r).map_err(|err| SerializationError(Arc::new(err)))?;

    let mut append_value = |value: RawValue| {
        let cell_writer = writer.make_cell_writer();
        let _proof = match value {
            RawValue::Null => cell_writer.set_null(),
            RawValue::Unset => cell_writer.set_unset(),
            // The unwrap below will succeed because the value was successfully
            // deserialized from the CQL format, so it must have
            RawValue::Value(v) => cell_writer.set_value(v).unwrap(),
        };
    };

    if !serialized.has_names() {
        serialized.iter().for_each(append_value);
    } else {
        let values_by_name = serialized
            .iter_name_value_pairs()
            .map(|(k, v)| (k.unwrap(), v))
            .collect::<HashMap<_, _>>();

        for col in ctx.columns() {
            let val = values_by_name.get(col.name.as_str()).ok_or_else(|| {
                SerializationError(Arc::new(
                    ValueListToSerializeRowAdapterError::NoBindMarkerWithName {
                        name: col.name.clone(),
                    },
                ))
            })?;
            append_value(*val);
        }
    }

    Ok(())
}

/// Failed to type check values for a statement, represented by one of the types
/// built into the driver.
#[derive(Debug, Error, Clone)]
#[error("Failed to type check query arguments {rust_name}: {kind}")]
pub struct BuiltinTypeCheckError {
    /// Name of the Rust type used to represent the values.
    pub rust_name: &'static str,

    /// Detailed information about the failure.
    pub kind: BuiltinTypeCheckErrorKind,
}

fn mk_typck_err<T>(kind: impl Into<BuiltinTypeCheckErrorKind>) -> SerializationError {
    mk_typck_err_named(std::any::type_name::<T>(), kind)
}

fn mk_typck_err_named(
    name: &'static str,
    kind: impl Into<BuiltinTypeCheckErrorKind>,
) -> SerializationError {
    SerializationError::new(BuiltinTypeCheckError {
        rust_name: name,
        kind: kind.into(),
    })
}

/// Failed to serialize values for a statement, represented by one of the types
/// built into the driver.
#[derive(Debug, Error, Clone)]
#[error("Failed to serialize query arguments {rust_name}: {kind}")]
pub struct BuiltinSerializationError {
    /// Name of the Rust type used to represent the values.
    pub rust_name: &'static str,

    /// Detailed information about the failure.
    pub kind: BuiltinSerializationErrorKind,
}

fn mk_ser_err<T>(kind: impl Into<BuiltinSerializationErrorKind>) -> SerializationError {
    mk_ser_err_named(std::any::type_name::<T>(), kind)
}

fn mk_ser_err_named(
    name: &'static str,
    kind: impl Into<BuiltinSerializationErrorKind>,
) -> SerializationError {
    SerializationError::new(BuiltinSerializationError {
        rust_name: name,
        kind: kind.into(),
    })
}

/// Describes why type checking values for a statement failed.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum BuiltinTypeCheckErrorKind {
    /// The Rust type expects `asked_for` column, but the query requires `actual`.
    WrongColumnCount { actual: usize, asked_for: usize },

    /// The Rust type provides a value for some column, but that column is not
    /// present in the statement.
    MissingValueForColumn { name: String },

    /// A value required by the statement is not provided by the Rust type.
    ColumnMissingForValue { name: String },

    /// A different column name was expected at given position.
    ColumnNameMismatch {
        rust_column_name: String,
        db_column_name: String,
    },
}

impl Display for BuiltinTypeCheckErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuiltinTypeCheckErrorKind::WrongColumnCount { actual, asked_for } => {
                write!(f, "wrong column count: the query requires {asked_for} columns, but {actual} were provided")
            }
            BuiltinTypeCheckErrorKind::MissingValueForColumn { name } => {
                write!(
                    f,
                    "value for column {name} was not provided, but the query requires it"
                )
            }
            BuiltinTypeCheckErrorKind::ColumnMissingForValue { name } => {
                write!(
                    f,
                    "value for column {name} was provided, but there is no bind marker for this column in the query"
                )
            }
            BuiltinTypeCheckErrorKind::ColumnNameMismatch { rust_column_name, db_column_name } => write!(
                f,
                "expected column with name {db_column_name} at given position, but the Rust field name is {rust_column_name}"
            ),
        }
    }
}

/// Describes why serializing values for a statement failed.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum BuiltinSerializationErrorKind {
    /// One of the columns failed to serialize.
    ColumnSerializationFailed {
        name: String,
        err: SerializationError,
    },
}

impl Display for BuiltinSerializationErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuiltinSerializationErrorKind::ColumnSerializationFailed { name, err } => {
                write!(f, "failed to serialize column {name}: {err}")
            }
        }
    }
}

#[derive(Error, Debug)]
pub enum ValueListToSerializeRowAdapterError {
    #[error("There is no bind marker with name {name}, but a value for it was provided")]
    NoBindMarkerWithName { name: String },
}

/// A buffer containing already serialized values.
///
/// It is not aware of the types of contained values,
/// it is basically a byte buffer in the format expected by the CQL protocol.
/// Usually there is no need for a user of a driver to use this struct, it is mostly internal.
/// The exception are APIs like `ClusterData::compute_token` / `ClusterData::get_endpoints`.
/// Allows adding new values to the buffer and iterating over the content.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SerializedValues {
    serialized_values: Vec<u8>,
    element_count: u16,
}

impl SerializedValues {
    pub const fn new() -> Self {
        SerializedValues {
            serialized_values: Vec::new(),
            element_count: 0,
        }
    }

    /// A const empty instance, useful for taking references
    pub const EMPTY: &'static SerializedValues = &SerializedValues::new();

    pub fn from_serializable<T: SerializeRow>(
        ctx: &RowSerializationContext,
        row: &T,
    ) -> Result<Self, SerializationError> {
        let mut data = Vec::new();
        let element_count = {
            let mut writer = RowWriter::new(&mut data);
            row.serialize(ctx, &mut writer)?;
            match writer.value_count().try_into() {
                Ok(n) => n,
                Err(_) => {
                    return Err(SerializationError(Arc::new(
                        SerializeValuesError::TooManyValues,
                    )))
                }
            }
        };

        Ok(SerializedValues {
            serialized_values: data,
            element_count,
        })
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.element_count() == 0
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = RawValue> {
        SerializedValuesIterator {
            serialized_values: &self.serialized_values,
        }
    }

    #[inline]
    pub fn element_count(&self) -> u16 {
        // We initialize first two bytes in new() and BufBackedRowWriter does too,
        // so this unwrap is safe
        self.element_count
    }

    #[inline]
    pub fn buffer_size(&self) -> usize {
        self.serialized_values.len()
    }

    pub(crate) fn write_to_request(&self, buf: &mut impl BufMut) {
        buf.put_u16(self.element_count);
        buf.put(self.serialized_values.as_slice())
    }

    /// Serializes value and appends it to the list
    pub fn add_value<T: SerializeCql>(
        &mut self,
        val: &T,
        typ: &ColumnType,
    ) -> Result<(), SerializationError> {
        if self.element_count() == u16::MAX {
            return Err(SerializationError(Arc::new(
                SerializeValuesError::TooManyValues,
            )));
        }

        let len_before_serialize: usize = self.serialized_values.len();

        let writer = CellWriter::new(&mut self.serialized_values);
        if let Err(e) = val.serialize(typ, writer) {
            self.serialized_values.resize(len_before_serialize, 0);
            Err(e)
        } else {
            self.element_count += 1;
            Ok(())
        }
    }

    /// Creates value list from the request frame
    pub(crate) fn new_from_frame(buf: &mut &[u8]) -> Result<Self, ParseError> {
        let values_num = types::read_short(buf)?;
        let values_beg = *buf;
        for _ in 0..values_num {
            let _serialized = types::read_value(buf)?;
        }

        let values_len_in_buf = values_beg.len() - buf.len();
        let values_in_frame = &values_beg[0..values_len_in_buf];
        Ok(SerializedValues {
            serialized_values: values_in_frame.to_vec(),
            element_count: values_num,
        })
    }

    // Temporary function, to be removed when we implement new batching API (right now it is needed in frame::request::mod.rs tests)
    pub fn to_old_serialized_values(&self) -> LegacySerializedValues {
        let mut frame = Vec::new();
        self.write_to_request(&mut frame);
        LegacySerializedValues::new_from_frame(&mut frame.as_slice(), false).unwrap()
    }
}

impl Default for SerializedValues {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy)]
pub struct SerializedValuesIterator<'a> {
    serialized_values: &'a [u8],
}

impl<'a> Iterator for SerializedValuesIterator<'a> {
    type Item = RawValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.serialized_values.is_empty() {
            return None;
        }

        Some(types::read_value(&mut self.serialized_values).expect("badly encoded value"))
    }
}

#[cfg(test)]
mod tests {
    use crate::frame::response::result::{ColumnSpec, ColumnType, TableSpec};
    use crate::frame::types::RawValue;
    use crate::frame::value::{LegacySerializedValues, MaybeUnset, ValueList};
    use crate::types::serialize::RowWriter;

    use super::{
        BuiltinSerializationError, BuiltinSerializationErrorKind, BuiltinTypeCheckError,
        BuiltinTypeCheckErrorKind, RowSerializationContext, SerializeCql, SerializeRow,
    };

    use super::SerializedValues;
    use scylla_macros::SerializeRow;

    fn col_spec(name: &str, typ: ColumnType) -> ColumnSpec {
        ColumnSpec {
            table_spec: TableSpec {
                ks_name: "ks".to_string(),
                table_name: "tbl".to_string(),
            },
            name: name.to_string(),
            typ,
        }
    }

    #[test]
    fn test_legacy_fallback() {
        let row = (
            1i32,
            "Ala ma kota",
            None::<i64>,
            MaybeUnset::Unset::<String>,
        );

        let mut legacy_data = Vec::new();
        <_ as ValueList>::write_to_request(&row, &mut legacy_data).unwrap();

        let mut new_data = Vec::new();
        let mut new_data_writer = RowWriter::new(&mut new_data);
        let ctx = RowSerializationContext {
            columns: &[
                col_spec("a", ColumnType::Int),
                col_spec("b", ColumnType::Text),
                col_spec("c", ColumnType::BigInt),
                col_spec("b", ColumnType::Ascii),
            ],
        };
        <_ as SerializeRow>::serialize(&row, &ctx, &mut new_data_writer).unwrap();
        assert_eq!(new_data_writer.value_count(), 4);

        // Skip the value count
        assert_eq!(&legacy_data[2..], new_data);
    }

    #[test]
    fn test_legacy_fallback_with_names() {
        let sorted_row = (
            1i32,
            "Ala ma kota",
            None::<i64>,
            MaybeUnset::Unset::<String>,
        );

        let mut sorted_row_data = Vec::new();
        <_ as ValueList>::write_to_request(&sorted_row, &mut sorted_row_data).unwrap();

        let mut unsorted_row = LegacySerializedValues::new();
        unsorted_row.add_named_value("a", &1i32).unwrap();
        unsorted_row.add_named_value("b", &"Ala ma kota").unwrap();
        unsorted_row
            .add_named_value("d", &MaybeUnset::Unset::<String>)
            .unwrap();
        unsorted_row.add_named_value("c", &None::<i64>).unwrap();

        let mut unsorted_row_data = Vec::new();
        let mut unsorted_row_data_writer = RowWriter::new(&mut unsorted_row_data);
        let ctx = RowSerializationContext {
            columns: &[
                col_spec("a", ColumnType::Int),
                col_spec("b", ColumnType::Text),
                col_spec("c", ColumnType::BigInt),
                col_spec("d", ColumnType::Ascii),
            ],
        };
        <_ as SerializeRow>::serialize(&unsorted_row, &ctx, &mut unsorted_row_data_writer).unwrap();
        assert_eq!(unsorted_row_data_writer.value_count(), 4);

        // Skip the value count
        assert_eq!(&sorted_row_data[2..], unsorted_row_data);
    }

    #[test]
    fn test_dyn_serialize_row() {
        let row = (
            1i32,
            "Ala ma kota",
            None::<i64>,
            MaybeUnset::Unset::<String>,
        );
        let ctx = RowSerializationContext {
            columns: &[
                col_spec("a", ColumnType::Int),
                col_spec("b", ColumnType::Text),
                col_spec("c", ColumnType::BigInt),
                col_spec("d", ColumnType::Ascii),
            ],
        };

        let mut typed_data = Vec::new();
        let mut typed_data_writer = RowWriter::new(&mut typed_data);
        <_ as SerializeRow>::serialize(&row, &ctx, &mut typed_data_writer).unwrap();

        let row = &row as &dyn SerializeRow;
        let mut erased_data = Vec::new();
        let mut erased_data_writer = RowWriter::new(&mut erased_data);
        <_ as SerializeRow>::serialize(&row, &ctx, &mut erased_data_writer).unwrap();

        assert_eq!(
            typed_data_writer.value_count(),
            erased_data_writer.value_count(),
        );
        assert_eq!(typed_data, erased_data);
    }

    fn do_serialize<T: SerializeRow>(t: T, columns: &[ColumnSpec]) -> Vec<u8> {
        let ctx = RowSerializationContext { columns };
        let mut ret = Vec::new();
        let mut builder = RowWriter::new(&mut ret);
        t.serialize(&ctx, &mut builder).unwrap();
        ret
    }

    fn col(name: &str, typ: ColumnType) -> ColumnSpec {
        ColumnSpec {
            table_spec: TableSpec {
                ks_name: "ks".to_string(),
                table_name: "tbl".to_string(),
            },
            name: name.to_string(),
            typ,
        }
    }

    // Do not remove. It's not used in tests but we keep it here to check that
    // we properly ignore warnings about unused variables, unnecessary `mut`s
    // etc. that usually pop up when generating code for empty structs.
    #[derive(SerializeRow)]
    #[scylla(crate = crate)]
    struct TestRowWithNoColumns {}

    #[derive(SerializeRow, Debug, PartialEq, Eq, Default)]
    #[scylla(crate = crate)]
    struct TestRowWithColumnSorting {
        a: String,
        b: i32,
        c: Vec<i64>,
    }

    #[test]
    fn test_row_serialization_with_column_sorting_correct_order() {
        let spec = [
            col("a", ColumnType::Text),
            col("b", ColumnType::Int),
            col("c", ColumnType::List(Box::new(ColumnType::BigInt))),
        ];

        let reference = do_serialize(("Ala ma kota", 42i32, vec![1i64, 2i64, 3i64]), &spec);
        let row = do_serialize(
            TestRowWithColumnSorting {
                a: "Ala ma kota".to_owned(),
                b: 42,
                c: vec![1, 2, 3],
            },
            &spec,
        );

        assert_eq!(reference, row);
    }

    #[test]
    fn test_row_serialization_with_column_sorting_incorrect_order() {
        // The order of two last columns is swapped
        let spec = [
            col("a", ColumnType::Text),
            col("c", ColumnType::List(Box::new(ColumnType::BigInt))),
            col("b", ColumnType::Int),
        ];

        let reference = do_serialize(("Ala ma kota", vec![1i64, 2i64, 3i64], 42i32), &spec);
        let row = do_serialize(
            TestRowWithColumnSorting {
                a: "Ala ma kota".to_owned(),
                b: 42,
                c: vec![1, 2, 3],
            },
            &spec,
        );

        assert_eq!(reference, row);
    }

    #[test]
    fn test_row_serialization_failing_type_check() {
        let row = TestRowWithColumnSorting::default();
        let mut data = Vec::new();
        let mut row_writer = RowWriter::new(&mut data);

        let spec_without_c = [
            col("a", ColumnType::Text),
            col("b", ColumnType::Int),
            // Missing column c
        ];

        let ctx = RowSerializationContext {
            columns: &spec_without_c,
        };
        let err = <_ as SerializeRow>::serialize(&row, &ctx, &mut row_writer).unwrap_err();
        let err = err.0.downcast_ref::<BuiltinTypeCheckError>().unwrap();
        assert!(matches!(
            err.kind,
            BuiltinTypeCheckErrorKind::ColumnMissingForValue { .. }
        ));

        let spec_duplicate_column = [
            col("a", ColumnType::Text),
            col("b", ColumnType::Int),
            col("c", ColumnType::List(Box::new(ColumnType::BigInt))),
            // Unexpected last column
            col("d", ColumnType::Counter),
        ];

        let ctx = RowSerializationContext {
            columns: &spec_duplicate_column,
        };
        let err = <_ as SerializeRow>::serialize(&row, &ctx, &mut row_writer).unwrap_err();
        let err = err.0.downcast_ref::<BuiltinTypeCheckError>().unwrap();
        assert!(matches!(
            err.kind,
            BuiltinTypeCheckErrorKind::MissingValueForColumn { .. }
        ));

        let spec_wrong_type = [
            col("a", ColumnType::Text),
            col("b", ColumnType::Int),
            col("c", ColumnType::TinyInt), // Wrong type
        ];

        let ctx = RowSerializationContext {
            columns: &spec_wrong_type,
        };
        let err = <_ as SerializeRow>::serialize(&row, &ctx, &mut row_writer).unwrap_err();
        let err = err.0.downcast_ref::<BuiltinSerializationError>().unwrap();
        assert!(matches!(
            err.kind,
            BuiltinSerializationErrorKind::ColumnSerializationFailed { .. }
        ));
    }

    #[derive(SerializeRow)]
    #[scylla(crate = crate)]
    struct TestRowWithGenerics<'a, T: SerializeCql> {
        a: &'a str,
        b: T,
    }

    #[test]
    fn test_row_serialization_with_generics() {
        // A minimal smoke test just to test that it works.
        fn check_with_type<T: SerializeCql + Copy>(typ: ColumnType, t: T) {
            let spec = [col("a", ColumnType::Text), col("b", typ)];
            let reference = do_serialize(("Ala ma kota", t), &spec);
            let row = do_serialize(
                TestRowWithGenerics {
                    a: "Ala ma kota",
                    b: t,
                },
                &spec,
            );
            assert_eq!(reference, row);
        }

        check_with_type(ColumnType::Int, 123_i32);
        check_with_type(ColumnType::Double, 123_f64);
    }

    #[derive(SerializeRow, Debug, PartialEq, Eq, Default)]
    #[scylla(crate = crate, flavor = "enforce_order")]
    struct TestRowWithEnforcedOrder {
        a: String,
        b: i32,
        c: Vec<i64>,
    }

    #[test]
    fn test_row_serialization_with_enforced_order_correct_order() {
        let spec = [
            col("a", ColumnType::Text),
            col("b", ColumnType::Int),
            col("c", ColumnType::List(Box::new(ColumnType::BigInt))),
        ];

        let reference = do_serialize(("Ala ma kota", 42i32, vec![1i64, 2i64, 3i64]), &spec);
        let row = do_serialize(
            TestRowWithEnforcedOrder {
                a: "Ala ma kota".to_owned(),
                b: 42,
                c: vec![1, 2, 3],
            },
            &spec,
        );

        assert_eq!(reference, row);
    }

    #[test]
    fn test_row_serialization_with_enforced_order_failing_type_check() {
        let row = TestRowWithEnforcedOrder::default();
        let mut data = Vec::new();
        let mut writer = RowWriter::new(&mut data);

        // The order of two last columns is swapped
        let spec = [
            col("a", ColumnType::Text),
            col("c", ColumnType::List(Box::new(ColumnType::BigInt))),
            col("b", ColumnType::Int),
        ];
        let ctx = RowSerializationContext { columns: &spec };
        let err = <_ as SerializeRow>::serialize(&row, &ctx, &mut writer).unwrap_err();
        let err = err.0.downcast_ref::<BuiltinTypeCheckError>().unwrap();
        assert!(matches!(
            err.kind,
            BuiltinTypeCheckErrorKind::ColumnNameMismatch { .. }
        ));

        let spec_without_c = [
            col("a", ColumnType::Text),
            col("b", ColumnType::Int),
            // Missing column c
        ];

        let ctx = RowSerializationContext {
            columns: &spec_without_c,
        };
        let err = <_ as SerializeRow>::serialize(&row, &ctx, &mut writer).unwrap_err();
        let err = err.0.downcast_ref::<BuiltinTypeCheckError>().unwrap();
        assert!(matches!(
            err.kind,
            BuiltinTypeCheckErrorKind::ColumnMissingForValue { .. }
        ));

        let spec_duplicate_column = [
            col("a", ColumnType::Text),
            col("b", ColumnType::Int),
            col("c", ColumnType::List(Box::new(ColumnType::BigInt))),
            // Unexpected last column
            col("d", ColumnType::Counter),
        ];

        let ctx = RowSerializationContext {
            columns: &spec_duplicate_column,
        };
        let err = <_ as SerializeRow>::serialize(&row, &ctx, &mut writer).unwrap_err();
        let err = err.0.downcast_ref::<BuiltinTypeCheckError>().unwrap();
        assert!(matches!(
            err.kind,
            BuiltinTypeCheckErrorKind::MissingValueForColumn { .. }
        ));

        let spec_wrong_type = [
            col("a", ColumnType::Text),
            col("b", ColumnType::Int),
            col("c", ColumnType::TinyInt), // Wrong type
        ];

        let ctx = RowSerializationContext {
            columns: &spec_wrong_type,
        };
        let err = <_ as SerializeRow>::serialize(&row, &ctx, &mut writer).unwrap_err();
        let err = err.0.downcast_ref::<BuiltinSerializationError>().unwrap();
        assert!(matches!(
            err.kind,
            BuiltinSerializationErrorKind::ColumnSerializationFailed { .. }
        ));
    }

    #[test]
    fn test_empty_serialized_values() {
        let values = SerializedValues::new();
        assert!(values.is_empty());
        assert_eq!(values.element_count(), 0);
        assert_eq!(values.buffer_size(), 0);
        assert_eq!(values.iter().count(), 0);
    }

    #[test]
    fn test_serialized_values_content() {
        let mut values = SerializedValues::new();
        values.add_value(&1234i32, &ColumnType::Int).unwrap();
        values.add_value(&"abcdefg", &ColumnType::Ascii).unwrap();
        let mut buf = Vec::new();
        values.write_to_request(&mut buf);
        assert_eq!(
            buf,
            [
                0, 2, // element count
                0, 0, 0, 4, // size of int
                0, 0, 4, 210, // content of int (1234)
                0, 0, 0, 7, // size of string
                97, 98, 99, 100, 101, 102, 103, // content of string ('abcdefg')
            ]
        )
    }

    #[test]
    fn test_serialized_values_iter() {
        let mut values = SerializedValues::new();
        values.add_value(&1234i32, &ColumnType::Int).unwrap();
        values.add_value(&"abcdefg", &ColumnType::Ascii).unwrap();

        let mut iter = values.iter();
        assert_eq!(iter.next(), Some(RawValue::Value(&[0, 0, 4, 210])));
        assert_eq!(
            iter.next(),
            Some(RawValue::Value(&[97, 98, 99, 100, 101, 102, 103]))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_serialized_values_max_capacity() {
        let mut values = SerializedValues::new();
        for _ in 0..65535 {
            values
                .add_value(&123456789i64, &ColumnType::BigInt)
                .unwrap();
        }

        // Adding this value should fail, we reached max capacity
        values
            .add_value(&123456789i64, &ColumnType::BigInt)
            .unwrap_err();

        assert_eq!(values.iter().count(), 65535);
        assert!(values
            .iter()
            .all(|v| v == RawValue::Value(&[0, 0, 0, 0, 0x07, 0x5b, 0xcd, 0x15])))
    }
}
