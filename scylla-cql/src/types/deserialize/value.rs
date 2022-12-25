use crate::frame::frame_errors::ParseError;
use crate::frame::response::result::{deser_cql_value, ColumnType, CqlValue};

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

impl<'rows> FromCql<'rows> for CqlValue {
    fn type_check(_typ: &ColumnType) -> Result<(), ParseError> {
        // Type checking is done in deserialize
        Ok(())
    }

    fn deserialize(v: RawValue<'rows>) -> Result<Self, ParseError> {
        let mut val = ensure_not_null(v.value)?;
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

fn ensure_not_null(v: Option<&[u8]>) -> Result<&[u8], ParseError> {
    v.ok_or_else(|| ParseError::BadIncomingData("expected a non-null value".to_string()))
}
