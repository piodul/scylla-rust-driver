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

macro_rules! impl_tuple {
    ($($Ti:ident),*; $($idx:literal),*; $($idf:ident),*) => {
        impl<'rows, $($Ti),*> FromRow<'rows> for ($($Ti,)*)
        where
            $($Ti: FromCql<'rows>),*
        {
            fn type_check(specs: &[ColumnSpec]) -> Result<(), ParseError> {
                if let [$($idf),*] = &specs {
                    $(
                        <$Ti as FromCql<'rows>>::type_check(&$idf.typ)?;
                    )*
                    return Ok(());
                }
                const TUPLE_LEN: usize = [0, $($idx),*].len() - 1;
                return Err(ParseError::BadIncomingData(format!(
                    "Expected {} columns, but got {:?}",
                    TUPLE_LEN, specs.len(),
                )));
            }

            fn deserialize(mut row: ValueIterator<'rows>) -> Result<Self, ParseError> {
                const TUPLE_LEN: usize = [0, $($idx),*].len() - 1;
                let ret = (
                    $({
                        let raw = row.next().ok_or_else(|| ParseError::BadIncomingData(
                            format!("Expected {} values, got {}", TUPLE_LEN, $idx)
                        ))??;
                        <$Ti as FromCql<'rows>>::deserialize(raw)?
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
