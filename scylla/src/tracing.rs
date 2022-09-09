use crate::statement::Consistency;
use std::collections::HashMap;
use std::net::IpAddr;
use std::num::NonZeroU32;
use std::time::Duration;
use uuid::Uuid;

use crate::cql_to_rust::{FromRow, FromRowError};
use crate::frame::response::raw_result::{DeserializableFromRow, ValueIterator};
use crate::frame::response::result::ColumnSpec;
use crate::frame::response::result::Row;
use crate::frame::{frame_errors::ParseError, value::Time};

/// Tracing info retrieved from `system_traces.sessions`
/// with all events from `system_traces.events`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TracingInfo {
    pub client: Option<IpAddr>,
    pub command: Option<String>,
    pub coordinator: Option<IpAddr>,
    pub duration: Option<i32>,
    pub parameters: Option<HashMap<String, String>>,
    pub request: Option<String>,
    /// started_at is a timestamp - time since unix epoch
    pub started_at: Option<chrono::Duration>,

    pub events: Vec<TracingEvent>,
}

/// A single event happening during a traced query
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TracingEvent {
    pub event_id: Uuid,
    pub activity: Option<String>,
    pub source: Option<IpAddr>,
    pub source_elapsed: Option<i32>,
    pub thread: Option<String>,
}

/// Used to configure a custom retry strategy when querying tracing info
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GetTracingConfig {
    /// Number of attempts to be made before giving up.
    /// Default value: 5
    pub attempts: NonZeroU32,
    /// Interval to wait between each attempt.
    /// Default value: 3 milliseconds
    pub interval: Duration,
    /// Consistency to use in queries that read TracingInfo.
    /// Default value: One
    pub consistency: Consistency,
}

impl Default for GetTracingConfig {
    fn default() -> GetTracingConfig {
        GetTracingConfig {
            attempts: NonZeroU32::new(5).unwrap(),
            interval: Duration::from_millis(3),
            consistency: Consistency::One,
        }
    }
}

// A query used to query TracingInfo from system_traces.sessions
pub(crate) const TRACES_SESSION_QUERY_STR: &str =
    "SELECT client, command, coordinator, duration, parameters, request, started_at \
    FROM system_traces.sessions WHERE session_id = ?";

// A query used to query TracingEvent from system_traces.events
pub(crate) const TRACES_EVENTS_QUERY_STR: &str =
    "SELECT event_id, activity, source, source_elapsed, thread \
    FROM system_traces.events WHERE session_id = ?";

type TracingInfoTuple = (
    Option<IpAddr>,
    Option<String>,
    Option<IpAddr>,
    Option<i32>,
    Option<HashMap<String, String>>,
    Option<String>,
    Option<Time>,
);

impl<'rows> DeserializableFromRow<'rows> for TracingInfo {
    type Target = Self;

    fn type_check(typs: &[ColumnSpec]) -> Result<(), ParseError> {
        <TracingInfoTuple as DeserializableFromRow<'rows>>::type_check(typs)
    }

    fn deserialize(row: ValueIterator<'rows>) -> Result<Self::Target, ParseError> {
        let (client, command, coordinator, duration, parameters, request, started_at) =
            <TracingInfoTuple as DeserializableFromRow<'rows>>::deserialize(row)?;

        Ok(Self {
            client,
            command,
            coordinator,
            duration,
            parameters,
            request,
            started_at: started_at.map(|x| x.0),
            events: Vec::new(),
        })
    }
}

// Converts a row received by performing TRACES_SESSION_QUERY_STR to TracingInfo
impl FromRow for TracingInfo {
    fn from_row(row: Row) -> Result<TracingInfo, FromRowError> {
        let (client, command, coordinator, duration, parameters, request, started_at) =
            <(
                Option<IpAddr>,
                Option<String>,
                Option<IpAddr>,
                Option<i32>,
                Option<HashMap<String, String>>,
                Option<String>,
                Option<chrono::Duration>,
            )>::from_row(row)?;

        Ok(TracingInfo {
            client,
            command,
            coordinator,
            duration,
            parameters,
            request,
            started_at,
            events: Vec::new(),
        })
    }
}

type TracingEventTuple = (
    Uuid,
    Option<String>,
    Option<IpAddr>,
    Option<i32>,
    Option<String>,
);

impl<'rows> DeserializableFromRow<'rows> for TracingEvent {
    type Target = Self;

    fn type_check(typs: &[ColumnSpec]) -> Result<(), ParseError> {
        <TracingEventTuple as DeserializableFromRow<'rows>>::type_check(typs)
    }

    fn deserialize(row: ValueIterator<'rows>) -> Result<Self::Target, ParseError> {
        let (event_id, activity, source, source_elapsed, thread) =
            <TracingEventTuple as DeserializableFromRow<'rows>>::deserialize(row)?;

        Ok(Self {
            event_id,
            activity,
            source,
            source_elapsed,
            thread,
        })
    }
}

// Converts a row received by performing TRACES_SESSION_QUERY_STR to TracingInfo
impl FromRow for TracingEvent {
    fn from_row(row: Row) -> Result<TracingEvent, FromRowError> {
        let (event_id, activity, source, source_elapsed, thread) = <(
            Uuid,
            Option<String>,
            Option<IpAddr>,
            Option<i32>,
            Option<String>,
        )>::from_row(row)?;

        Ok(TracingEvent {
            event_id,
            activity,
            source,
            source_elapsed,
            thread,
        })
    }
}
