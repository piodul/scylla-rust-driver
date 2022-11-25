use super::value::FromCql;
use crate::frame::frame_errors::ParseError;
use crate::frame::response::result::ColumnSpec;

use super::ValueIterator;

// TODO: This has the same name as cql_to_rust::FromRow...
pub trait FromRow<'rows>
where
    Self: Sized,
{
    /// Checks whether this type can be deserialized from given CQL type.
    fn type_check(specs: &[ColumnSpec]) -> Result<(), ParseError>;

    /// Deserialize from given bytes.
    /// The function may assume that `type_check` was called and it succeeded.
    /// The length of `specs` must always be the same as `vs`.
    fn deserialize(row: ValueIterator<'rows>) -> Result<Self, ParseError>;
}

impl<'rows, T> FromRow<'rows> for Vec<T>
where
    T: FromCql<'rows>,
{
    fn type_check(specs: &[ColumnSpec]) -> Result<(), ParseError> {
        for spec in specs {
            T::type_check(&spec.typ)?;
        }
        Ok(())
    }

    fn deserialize(mut row: ValueIterator<'rows>) -> Result<Self, ParseError> {
        let mut ret = Vec::with_capacity(row.size_hint().0);
        while let Some(value) = row.next().transpose()? {
            ret.push(T::deserialize(value)?);
        }
        Ok(ret)
    }
}
