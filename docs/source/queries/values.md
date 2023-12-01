# Query values
Query text is constant, but the values might change.
You can pass changing values to a query by specifying a list of variables as bound values.\
Each `?` in query text will be filled with the matching value. 

> **Never** pass values by adding strings, this could lead to [SQL Injection](https://en.wikipedia.org/wiki/SQL_injection)

A list of values can be anything that implements the `SerializeRow` trait.
See the API docs for the `SerializeRow` for a complete list of types that implement that trait.

A few examples:
```rust
# extern crate scylla;
# use scylla::{Session, SerializeRow, frame::response::result::CqlValue};
# use std::error::Error;
# use std::collections::HashMap;
# async fn check_only_compiles(session: &Session) -> Result<(), Box<dyn Error>> {
// Empty slice means that there are no values to send
session.query("INSERT INTO ks.tab (a) VALUES(1)", &[]).await?;

// Empty tuple/unit also means that there are no values to send
session.query("INSERT INTO ks.tab (a) VALUES(1)", ()).await?;

// Sending three integers using a slice:
session
    .query("INSERT INTO ks.tab (a, b, c) VALUES(?, ?, ?)", [1_i32, 2, 3].as_ref())
    .await?;

// Sending an integer and a string using a tuple
session
    .query("INSERT INTO ks.tab (a, b) VALUES(?, ?)", (2_i32, "Some text"))
    .await?;

// Sending an integer and a string using a named struct.
#[derive(SerializeRow)]
struct IntString {
    a: i32,
    b: String,
}

let int_string = IntString {
    a: 42_i32,
    b: "hello".to_owned(),
};

// Note that the order of the fields does not have to correspond to the order
// of the columns in the query. The field "a" will be matched with the bind
// marker for column "a", and field "b" to column "b".
session
    .query("INSERT INTO ks.tab (b, a) VALUES(?, ?)", int_string)
    .await?;

// Sending a single value as a tuple requires a trailing coma (Rust syntax):
session.query("INSERT INTO ks.tab (a) VALUES(?)", (2_i32,)).await?;

// Each value can also be sent using a reference:
session
    .query("INSERT INTO ks.tab (a, b) VALUES(?, ?)", &(&2_i32, &"Some text"))
    .await?;

// Values can also be passed via a HashMap. Like in the case of struct fields,
// entries of the map are also matched by name. In this example, though,
// we are using named bind markers, so instead of using the column names,
// values are matched to the bind marker names.
let mut vals: HashMap<&str, CqlValue> = HashMap::new();
vals.insert("avalue", CqlValue::Text("hello".to_string()));
vals.insert("bvalue", CqlValue::Int(17));
session
    .query("INSERT INTO ks.tab (a, b) VALUES(:avalue, :bvalue)", &vals)
    .await?;

# Ok(())
# }
```

### `NULL` values
Null values can be sent using `Option<>` - sending a `None` will make the value `NULL`:
```rust
# extern crate scylla;
# use scylla::Session;
# use std::error::Error;
# async fn check_only_compiles(session: &Session) -> Result<(), Box<dyn Error>> {
let null_i32: Option<i32> = None;
session
    .query("INSERT INTO ks.tab (a) VALUES(?)", (null_i32,))
    .await?;
# Ok(())
# }
```

### `Unset` values
When performing an insert with values which might be `NULL`, it's better to use `Unset`.\
Database treats inserting `NULL` as a delete operation and will generate a tombstone.
Using `Unset` results in better performance:

```rust
# extern crate scylla;
# use scylla::Session;
# use std::error::Error;
# async fn check_only_compiles(session: &Session) -> Result<(), Box<dyn Error>> {
use scylla::frame::value::{MaybeUnset, Unset};

// Inserting a null results in suboptimal performance
let null_i32: Option<i32> = None;
session
    .query("INSERT INTO ks.tab (a) VALUES(?)", (null_i32,))
    .await?;

// Using MaybeUnset enum is better
let unset_i32: MaybeUnset<i32> = MaybeUnset::Unset;
session
    .query("INSERT INTO ks.tab (a) VALUES(?)", (unset_i32,))
    .await?;

// If we are sure that a value should be unset we can simply use Unset
session
    .query("INSERT INTO ks.tab (a) VALUES(?)", (Unset,))
    .await?;
# Ok(())
# }
```
See the [issue](https://issues.apache.org/jira/browse/CASSANDRA-7304) for more information about `Unset`

### Other data types
See [Data Types](../data-types/data-types.md) for instructions on sending other data types

## Legacy `ValueList` trait

The `SerializeRow` trait was introduced in 0.11 and took its role from the `ValueList` trait.
In order to make migration easier, the legacy `ValueList` is still present in the driver and it's easy to 

Before version 0.11, the trait `ValueList` was used instead of `SerializeRow`.
The 
