use crate::routing::{Shard, ShardCount, Sharder, Token};
use crate::transport::errors::QueryError;
use crate::transport::{
    connection,
    connection::{Connection, ConnectionConfig, ErrorReceiver, VerifiedKeyspaceName},
};

use arc_swap::ArcSwap;
use futures::{future::RemoteHandle, stream::FuturesUnordered, Future, FutureExt, StreamExt};
use rand::Rng;
use std::convert::TryInto;
use std::io::ErrorKind;
use std::net::{IpAddr, SocketAddr};
use std::num::NonZeroUsize;
use std::pin::Pin;
use std::sync::{Arc, Weak};
use std::time::Duration;
use tokio::sync::{mpsc, Notify};
use tracing::{debug, trace, warn};

/// The target size of a per-node connection pool.
#[derive(Debug, Clone)]
pub enum PoolSize {
    /// Indicates that the pool should establish given number of connections to the node.
    ///
    /// If this option is used with a Scylla cluster, it is not guaranteed that connections will be
    /// distributed evenly across shards. Use this option if you cannot use the shard-aware port
    /// and you suffer from the "connection storm" problems.
    PerHost(NonZeroUsize),

    /// Indicates that the pool should establish given number of connections to each shard on the node.
    ///
    /// Cassandra nodes will be treated as if they have only one shard.
    ///
    /// The recommended setting for Scylla is one connection per shard - `PerShard(1)`.
    PerShard(NonZeroUsize),
}

impl Default for PoolSize {
    fn default() -> Self {
        PoolSize::PerShard(NonZeroUsize::new(1).unwrap())
    }
}

#[derive(Clone)]
pub struct PoolConfig {
    pub connection_config: ConnectionConfig,
    pub pool_size: PoolSize,
    pub can_use_shard_aware_port: bool,
}

impl Default for PoolConfig {
    fn default() -> Self {
        Self {
            connection_config: Default::default(),
            pool_size: Default::default(),
            can_use_shard_aware_port: true,
        }
    }
}

enum MaybePoolConnections {
    // The pool is still being initialized
    Initializing,

    // The pool is empty and is waiting to be refilled
    Pending,

    // The pool has some connections which are usable (or will be removed soon)
    Ready(PoolConnections),
}

#[derive(Clone)]
enum PoolConnections {
    NotSharded(Vec<Arc<Connection>>),
    Sharded {
        sharder: Sharder,
        connections: Vec<Vec<Arc<Connection>>>,
    },
}

pub struct NodeConnectionPool {
    conns: Arc<ArcSwap<MaybePoolConnections>>,
    use_keyspace_request_sender: mpsc::Sender<UseKeyspaceRequest>,
    _refiller_handle: RemoteHandle<()>,
    pool_updated_notify: Arc<Notify>,
}

impl NodeConnectionPool {
    pub fn new(
        address: IpAddr,
        port: u16,
        pool_config: PoolConfig,
        current_keyspace: Option<VerifiedKeyspaceName>,
    ) -> Self {
        let (use_keyspace_request_sender, use_keyspace_request_receiver) = mpsc::channel(1);
        let pool_updated_notify = Arc::new(Notify::new());

        let refiller = PoolRefiller::new(
            address,
            port,
            pool_config,
            current_keyspace,
            pool_updated_notify.clone(),
        );

        let conns = refiller.get_shared_connections();
        let (fut, handle) = refiller.run(use_keyspace_request_receiver).remote_handle();
        tokio::spawn(fut);

        Self {
            conns,
            use_keyspace_request_sender,
            _refiller_handle: handle,
            pool_updated_notify,
        }
    }

    pub fn connection_for_token(&self, token: Token) -> Result<Arc<Connection>, QueryError> {
        self.with_connections(|pool_conns| match pool_conns {
            PoolConnections::NotSharded(conns) => {
                Self::choose_random_connection_from_slice(conns).unwrap()
            }
            PoolConnections::Sharded {
                sharder,
                connections,
            } => {
                let shard: u16 = sharder
                    .shard_of(token)
                    .try_into()
                    .expect("Shard number doesn't fit in u16");
                Self::connection_for_shard(shard, sharder.nr_shards, connections.as_slice())
            }
        })
    }

    pub fn random_connection(&self) -> Result<Arc<Connection>, QueryError> {
        self.with_connections(|pool_conns| match pool_conns {
            PoolConnections::NotSharded(conns) => {
                Self::choose_random_connection_from_slice(conns).unwrap()
            }
            PoolConnections::Sharded {
                sharder,
                connections,
            } => {
                let shard: u16 = rand::thread_rng().gen_range(0..sharder.nr_shards.get());
                Self::connection_for_shard(shard, sharder.nr_shards, connections.as_slice())
            }
        })
    }

    // Tries to get a connection to given shard, if it's broken returns any working connection
    fn connection_for_shard(
        shard: u16,
        nr_shards: ShardCount,
        shard_conns: &[Vec<Arc<Connection>>],
    ) -> Arc<Connection> {
        // Try getting the desired connection
        if let Some(conn) = Self::choose_random_connection_from_slice(&shard_conns[shard as usize])
        {
            return conn;
        }

        // If this fails try getting any other in random order
        let mut shards_to_try: Vec<u16> =
            (shard..nr_shards.get()).chain(0..shard).skip(1).collect();

        while !shards_to_try.is_empty() {
            let idx = rand::thread_rng().gen_range(0..shards_to_try.len());
            let shard = shards_to_try.swap_remove(idx);

            if let Some(conn) =
                Self::choose_random_connection_from_slice(&shard_conns[shard as usize])
            {
                return conn;
            }
        }

        unreachable!("could not find any connection in supposedly non-empty pool")
    }

    pub async fn use_keyspace(
        &self,
        keyspace_name: VerifiedKeyspaceName,
    ) -> Result<(), QueryError> {
        let (response_sender, response_receiver) = tokio::sync::oneshot::channel();

        self.use_keyspace_request_sender
            .send(UseKeyspaceRequest {
                keyspace_name,
                response_sender,
            })
            .await
            .expect("Bug in ConnectionKeeper::use_keyspace sending");
        // Other end of this channel is in the Refiller, can't be dropped while we have &self to _refiller_handle

        response_receiver.await.unwrap() // NodePoolRefiller always responds
    }

    pub async fn wait_until_initialized(&self) {
        // First, register for the notification
        // so that we don't miss it
        let notified = self.pool_updated_notify.notified();

        if let MaybePoolConnections::Initializing = **self.conns.load() {
            // If the pool is not initialized yet, wait until we get a notification
            notified.await;
        }
    }

    pub fn get_working_connections(&self) -> Result<Vec<Arc<Connection>>, QueryError> {
        self.with_connections(|pool_conns| match pool_conns {
            PoolConnections::NotSharded(conns) => conns.clone(),
            PoolConnections::Sharded { connections, .. } => {
                connections.iter().flatten().cloned().collect()
            }
        })
    }

    fn choose_random_connection_from_slice(v: &[Arc<Connection>]) -> Option<Arc<Connection>> {
        if v.is_empty() {
            None
        } else if v.len() == 1 {
            Some(v[0].clone())
        } else {
            let idx = rand::thread_rng().gen_range(0..v.len());
            Some(v[idx].clone())
        }
    }

    fn with_connections<T>(&self, f: impl FnOnce(&PoolConnections) -> T) -> Result<T, QueryError> {
        let conns = self.conns.load_full();
        match &*conns {
            MaybePoolConnections::Ready(pool_connections) => Ok(f(pool_connections)),
            _ => Err(QueryError::IoError(Arc::new(std::io::Error::new(
                ErrorKind::Other,
                "No connections in the pool",
            )))),
        }
    }
}

const EXCESS_CONNECTION_BOUND_PER_SHARD_MULTIPLIER: usize = 10;

// TODO: Make it configurable through a policy (issue #184)
const MIN_FILL_BACKOFF: Duration = Duration::from_millis(50);
const MAX_FILL_BACKOFF: Duration = Duration::from_secs(10);
const FILL_BACKOFF_MULTIPLIER: u32 = 2;

// A simple exponential strategy for pool fill backoffs.
struct RefillDelayStrategy {
    current_delay: Duration,
}

impl RefillDelayStrategy {
    fn new() -> Self {
        Self {
            current_delay: MIN_FILL_BACKOFF,
        }
    }

    fn get_delay(&self) -> Duration {
        self.current_delay
    }

    fn on_pool_full(&mut self) {
        self.current_delay = MIN_FILL_BACKOFF;
    }

    fn on_fill_error(&mut self) {
        self.current_delay = std::cmp::min(
            MAX_FILL_BACKOFF,
            self.current_delay * FILL_BACKOFF_MULTIPLIER,
        );
    }
}

struct PoolRefiller {
    // Following information identify the pool and do not change
    address: IpAddr,
    regular_port: u16,
    pool_config: PoolConfig,

    // Following fields are updated with information from OPTIONS
    shard_aware_port: Option<u16>,
    sharder: Option<Sharder>,

    // `shared_conns` is updated only after `conns` change
    shared_conns: Arc<ArcSwap<MaybePoolConnections>>,
    conns: Vec<Vec<Arc<Connection>>>,

    // Set to true if there was an error since the last refill,
    // set to false when refilling starts.
    had_error_since_last_refill: bool,

    refill_delay_strategy: RefillDelayStrategy,

    // Receives information about connections becoming ready, i.e. newly connected
    // or after its keyspace was correctly set.
    // TODO: This should probably be a channel
    ready_connections:
        FuturesUnordered<Pin<Box<dyn Future<Output = OpenedConnectionEvent> + Send + 'static>>>,

    // Receives information about breaking connections
    connection_errors:
        FuturesUnordered<Pin<Box<dyn Future<Output = BrokenConnectionEvent> + Send + 'static>>>,

    // When connecting, Scylla always assigns the shard which handles the least
    // number of connections. If there are some non-shard-aware clients
    // connected to the same node, they might cause the shard distribution
    // to be heavily biased and Scylla will be very reluctant to assign some shards.
    //
    // In order to combat this, if the pool is not full and we get a connection
    // for a shard which was already filled, we keep those additional connections
    // in order to affect how Scylla assigns shards. A similar method is used
    // in Scylla's forks of the java and gocql drivers.
    //
    // The number of those connections is bounded by the number of shards multiplied
    // by a constant factor, and are all closed when they exceed this number.
    excess_connections: Vec<Arc<Connection>>,

    current_keyspace: Option<VerifiedKeyspaceName>,

    // Signaled when the connection pool is updated
    pool_updated_notify: Arc<Notify>,
}

#[derive(Debug)]
struct UseKeyspaceRequest {
    keyspace_name: VerifiedKeyspaceName,
    response_sender: tokio::sync::oneshot::Sender<Result<(), QueryError>>,
}

impl PoolRefiller {
    pub fn new(
        address: IpAddr,
        port: u16,
        pool_config: PoolConfig,
        current_keyspace: Option<VerifiedKeyspaceName>,
        pool_updated_notify: Arc<Notify>,
    ) -> Self {
        // At the beginning, we assume the node does not have any shards
        // and assume that the node is a Cassandra node
        // TODO: To speed the connection process up, we could take information
        // about shards from another node, and assume that the new node will
        // have the same amount of shards
        let conns = vec![Vec::new()];
        let shared_conns = Arc::new(ArcSwap::new(Arc::new(MaybePoolConnections::Initializing)));

        Self {
            address,
            regular_port: port,
            pool_config,

            shard_aware_port: None,
            sharder: None,

            shared_conns,
            conns,

            had_error_since_last_refill: false,
            refill_delay_strategy: RefillDelayStrategy::new(),

            ready_connections: FuturesUnordered::new(),
            connection_errors: FuturesUnordered::new(),

            excess_connections: Vec::new(),

            current_keyspace,

            pool_updated_notify,
        }
    }

    pub fn get_shared_connections(&self) -> Arc<ArcSwap<MaybePoolConnections>> {
        self.shared_conns.clone()
    }

    // The main loop of the pool refiller
    pub async fn run(
        mut self,
        mut use_keyspace_request_receiver: mpsc::Receiver<UseKeyspaceRequest>,
    ) {
        debug!("[{}] Started asynchronous pool worker", self.address);

        let mut next_refill_time = tokio::time::Instant::now();
        let mut refill_scheduled = true;

        loop {
            tokio::select! {
                _ = tokio::time::sleep_until(next_refill_time), if refill_scheduled => {
                    self.had_error_since_last_refill = false;
                    self.start_filling();
                    refill_scheduled = false;
                }

                evt = self.ready_connections.select_next_some(), if !self.ready_connections.is_empty() => {
                    self.handle_ready_connection(evt);

                    if self.is_full() {
                        self.refill_delay_strategy.on_pool_full();
                        debug!(
                            "[{}] Pool is full, clearing {} excess connections",
                            self.address,
                            self.excess_connections.len()
                        );
                        self.excess_connections.clear();
                    }
                }

                evt = self.connection_errors.select_next_some(), if !self.connection_errors.is_empty() => {
                    if let Some(conn) = evt.connection.upgrade() {
                        debug!("[{}] Got error for connection {:p}: {:?}", self.address, Arc::as_ptr(&conn), evt.error);
                        self.remove_connection(conn);
                    }
                }

                req = use_keyspace_request_receiver.recv() => {
                    match req {
                        None => {
                            // The keyspace request channel is dropped.
                            // This means that the corresponding pool is dropped.
                            // We can stop here.
                            trace!("[{}] Keyspace request channel dropped, stopping asynchronous pool worker", self.address);
                            return;
                        }
                        Some(req) => {
                            debug!("[{}] Requested keyspace change: {}", self.address, req.keyspace_name.as_str());
                            let fut = self.use_keyspace(&req.keyspace_name);
                            let address = self.address;
                            tokio::task::spawn(async move {
                                let res = fut.await;
                                match &res {
                                    Ok(()) => debug!("[{}] Successfully changed current keyspace", address),
                                    Err(err) => warn!("[{}] Failed to change keyspace: {:?}", address, err),
                                }
                                let _ = req.response_sender.send(res);
                            });
                        }
                    }
                }
            }

            // Schedule refilling here
            if !refill_scheduled && self.need_filling() {
                if self.had_error_since_last_refill {
                    self.refill_delay_strategy.on_fill_error();
                }
                let delay = self.refill_delay_strategy.get_delay();
                debug!(
                    "[{}] Scheduling next refill in {} ms",
                    self.address,
                    delay.as_millis(),
                );

                next_refill_time = tokio::time::Instant::now() + delay;
                refill_scheduled = true;
            }
        }
    }

    fn is_filling(&self) -> bool {
        !self.ready_connections.is_empty()
    }

    fn is_full(&self) -> bool {
        match self.pool_config.pool_size {
            PoolSize::PerHost(target) => self.active_connection_count() >= target.get(),
            PoolSize::PerShard(target) => {
                self.conns.iter().all(|conns| conns.len() >= target.get())
            }
        }
    }

    fn need_filling(&self) -> bool {
        !self.is_filling() && !self.is_full()
    }

    fn can_use_shard_aware_port(&self) -> bool {
        self.sharder.is_some()
            && self.shard_aware_port.is_some()
            && self.pool_config.can_use_shard_aware_port
    }

    // Begins opening a number of connections in order to fill the connection pool.
    // Futures which open the connections are pushed to the `ready_connections`
    // FuturesUnordered structure, and their results are processed in the main loop.
    fn start_filling(&mut self) {
        if self.can_use_shard_aware_port() {
            // Only use the shard-aware port if we have a PerShard strategy
            if let PoolSize::PerShard(target) = self.pool_config.pool_size {
                // Try to fill up each shard up to `target` connections
                for (shard_id, shard_conns) in self.conns.iter().enumerate() {
                    trace!(
                        "[{}] Will open {} connections to shard {}",
                        self.address,
                        target.get().saturating_sub(shard_conns.len()),
                        shard_id,
                    );
                    for _ in shard_conns.len()..target.get() {
                        self.start_opening_connection(Some(shard_id as Shard));
                    }
                }
                return;
            }
        }
        // Calculate how many more connections we need to open in order
        // to achieve the target connection count.
        let to_open_count = match self.pool_config.pool_size {
            PoolSize::PerHost(target) => {
                target.get().saturating_sub(self.active_connection_count())
            }
            PoolSize::PerShard(target) => self
                .conns
                .iter()
                .map(|conns| target.get().saturating_sub(conns.len()))
                .sum::<usize>(),
        };
        // When connecting to Scylla through non-shard-aware port,
        // Scylla alone will choose shards for us. We hope that
        // they will distribute across shards in the way we want,
        // but we have no guarantee, so we might have to retry
        // connecting later.
        trace!(
            "[{}] Will open {} non-shard-aware connections",
            self.address,
            to_open_count,
        );
        for _ in 0..to_open_count {
            self.start_opening_connection(None);
        }
    }

    // Handles a newly opened connection and decides what to do with it.
    fn handle_ready_connection(&mut self, evt: OpenedConnectionEvent) {
        match evt.result {
            Err(err) => {
                if evt.requested_shard.is_some() {
                    // If we failed to connect to a shard-aware port,
                    // fall back to the non-shard-aware port.
                    // Don't set `had_error_since_last_refill` here;
                    // the shard-aware port might be unreachable, but
                    // the regular port might be reachable. If we set
                    // `had_error_since_last_refill` here, it would cause
                    // the backoff to increase on each refill. With
                    // the non-shard aware port, multiple refills are sometimes
                    // necessary, so increasing the backoff would delay
                    // filling the pool even if the non-shard-aware port works
                    // and does not cause any errors.
                    debug!(
                        "[{}] Failed to open connection to the shard-aware port: {:?}, will retry with regular port",
                        self.address,
                        err,
                    );
                    self.start_opening_connection(None);
                } else {
                    // Encountered an error while connecting to the non-shard-aware
                    // port. Set the `had_error_since_last_refill` flag so that
                    // the next refill will be delayed more than this one.
                    self.had_error_since_last_refill = true;
                    debug!(
                        "[{}] Failed to open connection to the non-shard-aware port: {:?}",
                        self.address, err,
                    );
                }
            }
            Ok((connection, error_receiver)) => {
                // Update sharding and optionally reshard
                let shard_info = connection.get_shard_info().as_ref();
                let sharder = shard_info.map(|s| s.get_sharder());
                let shard_id = shard_info.map_or(0, |s| s.shard as usize);
                self.maybe_reshard(sharder);

                // Update the shard-aware port
                if self.shard_aware_port != connection.get_shard_aware_port() {
                    debug!(
                        "[{}] Updating shard aware port: {:?}",
                        self.address,
                        connection.get_shard_aware_port(),
                    );
                    self.shard_aware_port = connection.get_shard_aware_port();
                }

                // Before the connection can be put to the pool, we need
                // to make sure that it uses appropriate keyspace
                if let Some(keyspace) = &self.current_keyspace {
                    if evt.keyspace_name.as_ref() != Some(keyspace) {
                        // Asynchronously start setting keyspace for this
                        // connection. It will be received on the ready
                        // connections channel and will travel through
                        // this logic again, to be finally put into
                        // the conns.
                        self.start_setting_keyspace_for_connection(
                            connection,
                            error_receiver,
                            evt.requested_shard,
                        );
                        return;
                    }
                }

                // Decide if the connection can be accepted, according to
                // the pool filling strategy
                let can_be_accepted = match self.pool_config.pool_size {
                    PoolSize::PerHost(target) => self.active_connection_count() < target.get(),
                    PoolSize::PerShard(target) => self.conns[shard_id].len() < target.get(),
                };

                if can_be_accepted {
                    // Don't complain and just put the connection to the pool.
                    // If this was a shard-aware port connection which missed
                    // the right shard, we still want to accept it
                    // because it fills our pool.
                    let conn = Arc::new(connection);
                    trace!(
                        "[{}] Adding connection {:p} to shard {} pool, now is {}",
                        self.address,
                        Arc::as_ptr(&conn),
                        shard_id,
                        self.conns[shard_id].len() + 1,
                    );

                    self.connection_errors
                        .push(wait_for_error(Arc::downgrade(&conn), error_receiver).boxed());
                    self.conns[shard_id].push(conn);

                    self.update_shared_conns();
                } else if evt.requested_shard.is_some() {
                    // This indicates that some shard-aware connections
                    // missed the target shard (probably due to NAT).
                    // Because we don't know how address translation
                    // works here, it's better to leave the task
                    // of choosing the shard to Scylla. We will retry
                    // immediately with a non-shard-aware port here.
                    debug!(
                        "[{}] Excess shard-aware port connection for shard {}; will retry with non-shard-aware port",
                        self.address,
                        shard_id,
                    );

                    self.start_opening_connection(None);
                } else {
                    // We got unlucky and Scylla didn't distribute
                    // shards across connections evenly.
                    // We will retry in the next iteration,
                    // for now put it into the excess connection
                    // pool.
                    let conn = Arc::new(connection);
                    trace!(
                        "[{}] Storing excess connection {:p} for shard {}",
                        self.address,
                        Arc::as_ptr(&conn),
                        shard_id,
                    );

                    self.connection_errors
                        .push(wait_for_error(Arc::downgrade(&conn), error_receiver).boxed());
                    self.excess_connections.push(conn);

                    let excess_connection_limit = self.excess_connection_limit();
                    if self.excess_connections.len() > excess_connection_limit {
                        debug!(
                            "[{}] Excess connection pool exceeded limit of {} connections - clearing",
                            self.address,
                            excess_connection_limit,
                        );
                        self.excess_connections.clear();
                    }
                }
            }
        }
    }

    fn start_opening_connection(&self, shard: Option<Shard>) {
        let cfg = self.pool_config.connection_config.clone();
        let fut = match (self.sharder.clone(), self.shard_aware_port, shard) {
            (Some(sharder), Some(port), Some(shard)) => {
                let shard_aware_address = (self.address, port).into();
                async move {
                    let result = open_connection_to_shard_aware_port(
                        shard_aware_address,
                        shard,
                        sharder.clone(),
                        &cfg,
                    )
                    .await;
                    OpenedConnectionEvent {
                        result,
                        requested_shard: Some(shard),
                        keyspace_name: None,
                    }
                }
                .boxed()
            }
            _ => {
                let non_shard_aware_address = (self.address, self.regular_port).into();
                async move {
                    let result =
                        connection::open_connection(non_shard_aware_address, None, cfg).await;
                    OpenedConnectionEvent {
                        result,
                        requested_shard: None,
                        keyspace_name: None,
                    }
                }
                .boxed()
            }
        };
        self.ready_connections.push(fut);
    }

    fn maybe_reshard(&mut self, new_sharder: Option<Sharder>) {
        if self.sharder == new_sharder {
            return;
        }

        debug!(
            "[{}] New sharder: {:?}, clearing all connections",
            self.address, new_sharder,
        );

        self.sharder = new_sharder.clone();

        // If the sharder has changed, we can throw away all previous connections.
        // All connections to the same live node will have the same sharder,
        // so the old ones will become dead very soon anyway.
        self.conns.clear();

        let shard_count = new_sharder.map_or(1, |s| s.nr_shards.get() as usize);
        self.conns.resize_with(shard_count, Vec::new);

        self.excess_connections.clear();
    }

    fn update_shared_conns(&mut self) {
        let new_conns = if !self.has_connections() {
            Arc::new(MaybePoolConnections::Pending)
        } else {
            let new_conns = if let Some(sharder) = self.sharder.as_ref() {
                debug_assert_eq!(self.conns.len(), sharder.nr_shards.get() as usize);
                PoolConnections::Sharded {
                    sharder: sharder.clone(),
                    connections: self.conns.clone(),
                }
            } else {
                debug_assert_eq!(self.conns.len(), 1);
                PoolConnections::NotSharded(self.conns[0].clone())
            };
            Arc::new(MaybePoolConnections::Ready(new_conns))
        };

        // Make the connection list available
        self.shared_conns.store(new_conns);

        // Notify potential waiters
        self.pool_updated_notify.notify_waiters();
    }

    fn remove_connection(&mut self, connection: Arc<Connection>) {
        let ptr = Arc::as_ptr(&connection);

        let maybe_remove_in_vec = |v: &mut Vec<Arc<Connection>>| -> bool {
            let maybe_idx = v
                .iter()
                .enumerate()
                .find(|(_, other_conn)| Arc::ptr_eq(&connection, other_conn))
                .map(|(idx, _)| idx);
            match maybe_idx {
                Some(idx) => {
                    v.swap_remove(idx);
                    true
                }
                None => false,
            }
        };

        // First, look it up in the shard bucket
        // We might have resharded, so the bucket might not exist anymore
        let shard_id = connection
            .get_shard_info()
            .as_ref()
            .map_or(0, |s| s.shard as usize);
        if shard_id < self.conns.len() && maybe_remove_in_vec(&mut self.conns[shard_id]) {
            trace!(
                "[{}] Connection {:p} removed from shard {} pool",
                self.address,
                ptr,
                shard_id
            );
            self.update_shared_conns();
            return;
        }

        // If we didn't find it, it might sit in the excess_connections bucket
        if maybe_remove_in_vec(&mut self.excess_connections) {
            trace!(
                "[{}] Connection {:p} removed from excess connection pool",
                self.address,
                ptr,
            );
            return;
        }

        trace!(
            "[{}] Connection {:p} was already removed",
            self.address,
            ptr,
        );
    }

    fn use_keyspace(
        &mut self,
        keyspace_name: &VerifiedKeyspaceName,
    ) -> impl Future<Output = Result<(), QueryError>> + Send + Sync + 'static {
        self.current_keyspace = Some(keyspace_name.clone());

        let mut conns = self.conns.clone();
        let keyspace_name = keyspace_name.clone();

        async move {
            if conns.is_empty() {
                return Ok(());
            }

            let mut use_keyspace_futures = Vec::new();

            for shard_conns in conns.iter_mut() {
                for conn in shard_conns.iter_mut() {
                    let fut = conn.use_keyspace(&keyspace_name);
                    use_keyspace_futures.push(fut);
                }
            }

            let use_keyspace_results: Vec<Result<(), QueryError>> =
                futures::future::join_all(use_keyspace_futures).await;

            // If there was at least one Ok and the rest were IoErrors we can return Ok
            // keyspace name is correct and will be used on broken connection on the next reconnect

            // If there were only IoErrors then return IoError
            // If there was an error different than IoError return this error - something is wrong

            let mut was_ok: bool = false;
            let mut io_error: Option<Arc<std::io::Error>> = None;

            for result in use_keyspace_results {
                match result {
                    Ok(()) => was_ok = true,
                    Err(err) => match err {
                        QueryError::IoError(io_err) => io_error = Some(io_err),
                        _ => return Err(err),
                    },
                }
            }

            if was_ok {
                return Ok(());
            }

            // We can unwrap io_error because use_keyspace_futures must be nonempty
            Err(QueryError::IoError(io_error.unwrap()))
        }
    }

    // Requires the keyspace to be set
    // Requires that the event is for a successful connection
    fn start_setting_keyspace_for_connection(
        &mut self,
        connection: Connection,
        error_receiver: ErrorReceiver,
        requested_shard: Option<Shard>,
    ) {
        // TODO: There should be a timeout for this

        let keyspace_name = self.current_keyspace.as_ref().cloned().unwrap();
        self.ready_connections.push(
            async move {
                let result = connection.use_keyspace(&keyspace_name).await;
                if let Err(err) = result {
                    warn!(
                        "[{}] Failed to set keyspace for new connection: {}",
                        connection.get_connect_address().ip(),
                        err,
                    );
                }
                OpenedConnectionEvent {
                    result: Ok((connection, error_receiver)),
                    requested_shard,
                    keyspace_name: Some(keyspace_name),
                }
            }
            .boxed(),
        );
    }

    fn has_connections(&self) -> bool {
        self.conns.iter().any(|v| !v.is_empty())
    }

    fn active_connection_count(&self) -> usize {
        self.conns.iter().map(Vec::len).sum::<usize>()
    }

    fn excess_connection_limit(&self) -> usize {
        match self.pool_config.pool_size {
            PoolSize::PerShard(target) => {
                EXCESS_CONNECTION_BOUND_PER_SHARD_MULTIPLIER * target.get()
            }

            // In PerHost mode we do not need to keep excess connections
            PoolSize::PerHost(_) => 0,
        }
    }
}

struct BrokenConnectionEvent {
    connection: Weak<Connection>,
    error: QueryError,
}

async fn wait_for_error(
    connection: Weak<Connection>,
    error_receiver: ErrorReceiver,
) -> BrokenConnectionEvent {
    BrokenConnectionEvent {
        connection,
        error: error_receiver.await.unwrap_or_else(|_| {
            QueryError::IoError(Arc::new(std::io::Error::new(
                ErrorKind::Other,
                "Connection broken",
            )))
        }),
    }
}

struct OpenedConnectionEvent {
    result: Result<(Connection, ErrorReceiver), QueryError>,
    requested_shard: Option<Shard>,
    keyspace_name: Option<VerifiedKeyspaceName>,
}

async fn open_connection_to_shard_aware_port(
    address: SocketAddr,
    shard: Shard,
    sharder: Sharder,
    connection_config: &ConnectionConfig,
) -> Result<(Connection, ErrorReceiver), QueryError> {
    // Create iterator over all possible source ports for this shard
    let source_port_iter = sharder.iter_source_ports_for_shard(shard);

    for port in source_port_iter {
        let connect_result =
            connection::open_connection(address, Some(port), connection_config.clone()).await;

        match connect_result {
            Err(err) if err.is_address_unavailable_for_use() => continue, // If we can't use this port, try the next one
            result => return result,
        }
    }

    // Tried all source ports for that shard, give up
    Err(QueryError::IoError(Arc::new(std::io::Error::new(
        std::io::ErrorKind::AddrInUse,
        "Could not find free source port for shard",
    ))))
}

#[cfg(test)]
mod tests {
    use super::open_connection_to_shard_aware_port;
    use crate::routing::{ShardCount, Sharder};
    use crate::transport::connection::ConnectionConfig;
    use std::net::{SocketAddr, ToSocketAddrs};

    // Open many connections to a node
    // Port collision should occur
    // If they are not handled this test will most likely fail
    #[tokio::test]
    async fn many_connections() {
        let connections_number = 512;

        let connect_address: SocketAddr = std::env::var("SCYLLA_URI")
            .unwrap_or_else(|_| "127.0.0.1:9042".to_string())
            .to_socket_addrs()
            .unwrap()
            .next()
            .unwrap();

        let connection_config = ConnectionConfig {
            compression: None,
            tcp_nodelay: true,
            #[cfg(feature = "ssl")]
            ssl_context: None,
            ..Default::default()
        };

        // This does not have to be the real sharder,
        // the test is only about port collisions, not connecting
        // to the right shard
        let sharder = Sharder::new(ShardCount::new(3).unwrap(), 12);

        // Open the connections
        let mut conns = Vec::new();

        for _ in 0..connections_number {
            conns.push(open_connection_to_shard_aware_port(
                connect_address,
                0,
                sharder.clone(),
                &connection_config,
            ));
        }

        let joined = futures::future::join_all(conns).await;

        // Check that each connection managed to connect successfully
        for res in joined {
            res.unwrap();
        }
    }
}
