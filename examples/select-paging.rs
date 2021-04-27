use anyhow::Result;
use futures::stream::StreamExt;
use scylla::{query::Query, Session, SessionBuilder};
use std::env;

#[tokio::main]
async fn main() -> Result<()> {
    let uri = env::var("SCYLLA_URI").unwrap_or_else(|_| "127.0.0.1:9042".to_string());

    println!("Connecting to {} ...", uri);

    let session: Session = SessionBuilder::new().known_node(uri).build().await?;

    session.query("CREATE KEYSPACE IF NOT EXISTS ks WITH REPLICATION = {'class' : 'SimpleStrategy', 'replication_factor' : 1}", &[]).await?;

    session
        .query(
            "CREATE TABLE IF NOT EXISTS ks.t (a int, b int, c text, primary key (a, b))",
            &[],
        )
        .await?;

    for i in 0..16_i32 {
        session
            .query(
                "INSERT INTO ks.t (a, b, c) VALUES (?, ?, 'abc')",
                (i, 2 * i),
            )
            .await?;
    }

    // Iterate through select result with paging
    let mut rows_stream = session
        .query_iter("SELECT a, b, c FROM ks.t", &[])
        .await?
        .into_typed::<(i32, i32, String)>();

    while let Some(next_row_res) = rows_stream.next().await {
        let (a, b, c) = next_row_res?;
        println!("a, b, c: {}, {}, {}", a, b, c);
    }

    let paged_query = Query::new("SELECT a, b, c FROM ks.t".to_owned()).with_page_size(1);
    let paging_state = session.query(paged_query, &[]).await?.paging_state;
    println!("Paging state: {:#?}", paging_state);

    let paged_prepared = session
        .prepare(Query::with_page_size(
            "SELECT a, b, c FROM ks.t".to_owned(),
            1,
        ))
        .await?;
    let paging_state_from_prepared = session.execute(&paged_prepared, &[]).await?.paging_state;
    println!(
        "Paging state from the prepared statement execution: {:#?}",
        paging_state_from_prepared
    );

    println!("Ok.");

    Ok(())
}
