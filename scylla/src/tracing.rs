use crate::statement::Consistency;
use itertools::Itertools;
use scylla_macros::DeserializeRow;
use std::collections::HashMap;
use std::net::IpAddr;
use std::num::NonZeroU32;
use std::time::Duration;
use uuid::Uuid;

/// Tracing info retrieved from `system_traces.sessions`
/// with all events from `system_traces.events`
#[derive(Debug, DeserializeRow, Clone, PartialEq, Eq)]
#[scylla(crate = "crate")]
pub struct TracingInfo {
    pub client: Option<IpAddr>,
    pub command: Option<String>,
    pub coordinator: Option<IpAddr>,
    pub duration: Option<i32>,
    pub parameters: Option<HashMap<String, String>>,
    pub request: Option<String>,
    /// started_at is a timestamp - time since unix epoch
    pub started_at: Option<chrono::Duration>,

    #[scylla(skip)]
    pub events: Vec<TracingEvent>,
}

/// A single event happening during a traced query
#[derive(Debug, DeserializeRow, Clone, PartialEq, Eq)]
#[scylla(crate = "crate")]
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

impl TracingInfo {
    /// Returns a list of unique nodes involved in the query
    pub fn nodes(&self) -> Vec<IpAddr> {
        self.events
            .iter()
            .filter_map(|e| e.source)
            .unique()
            .collect()
    }
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
