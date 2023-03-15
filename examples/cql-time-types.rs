// An example showing how to use time related types in queries
// Date, Time, Timestamp

use anyhow::Result;
use chrono::{Duration, NaiveDate};
use scylla::frame::value::{Date, Time, Timestamp};
use scylla::transport::session::LegacySession;
use scylla::SessionBuilder;
use std::env;

#[tokio::main]
async fn main() -> Result<()> {
    let uri = env::var("SCYLLA_URI").unwrap_or_else(|_| "127.0.0.1:9042".to_string());

    println!("Connecting to {} ...", uri);

    let session: LegacySession = SessionBuilder::new().known_node(uri).build().await?;

    session.query("CREATE KEYSPACE IF NOT EXISTS ks WITH REPLICATION = {'class' : 'SimpleStrategy', 'replication_factor' : 1}", &[]).await?;

    // Date
    // Date is a year, month and day in the range -5877641-06-23 to -5877641-06-23

    session
        .query(
            "CREATE TABLE IF NOT EXISTS ks.dates (d date primary key)",
            &[],
        )
        .await?;

    // Dates in the range -262145-1-1 to 262143-12-31 can be represented using chrono::NaiveDate
    let example_date: NaiveDate = NaiveDate::from_ymd_opt(2020, 2, 20).unwrap();

    session
        .query("INSERT INTO ks.dates (d) VALUES (?)", (example_date,))
        .await?;

    let result = session.query("SELECT d from ks.dates", &[]).await?;
    let mut iter = result.rows_typed::<(NaiveDate,)>()?;
    while let Some((read_date,)) = iter.next().transpose()? {
        println!("Read a date: {:?}", read_date);
    }

    // Dates outside this range must be represented in the raw form - an u32 describing days since -5877641-06-23
    let example_big_date: Date = Date(u32::MAX);
    session
        .query("INSERT INTO ks.dates (d) VALUES (?)", (example_big_date,))
        .await?;

    let result = session.query("SELECT d from ks.dates", &[]).await?;
    let mut iter = result.rows_typed::<(Date,)>()?;
    while let Some((read_days,)) = iter.next().transpose()? {
        println!("Read a date as raw days: {}", read_days.0);
    }

    // Time - nanoseconds since midnight in range 0..=86399999999999
    let example_time: Duration = Duration::hours(1);

    session
        .query(
            "CREATE TABLE IF NOT EXISTS ks.times (t time primary key)",
            &[],
        )
        .await?;

    // Time as bound value must be wrapped in value::Time to differentiate from Timestamp
    session
        .query("INSERT INTO ks.times (t) VALUES (?)", (Time(example_time),))
        .await?;

    let result = session.query("SELECT t from ks.times", &[]).await?;
    let mut iter = result.rows_typed::<(Duration,)>()?;
    while let Some((read_time,)) = iter.next().transpose()? {
        println!("Read a time: {:?}", read_time);
    }

    // Timestamp - milliseconds since unix epoch - 1970-01-01
    let example_timestamp: Duration = Duration::hours(1); // This will describe 1970-01-01 01:00:00

    session
        .query(
            "CREATE TABLE IF NOT EXISTS ks.timestamps (t timestamp primary key)",
            &[],
        )
        .await?;

    // Timestamp as bound value must be wrapped in value::Timestamp to differentiate from Time
    session
        .query(
            "INSERT INTO ks.timestamps (t) VALUES (?)",
            (Timestamp(example_timestamp),),
        )
        .await?;

    let result = session.query("SELECT t from ks.timestamps", &[]).await?;
    let mut iter = result.rows_typed::<(Duration,)>()?;
    while let Some((read_time,)) = iter.next().transpose()? {
        println!("Read a timestamp: {:?}", read_time);
    }

    Ok(())
}
