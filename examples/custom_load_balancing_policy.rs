use anyhow::Result;
use scylla::{
    load_balancing::{LoadBalancingPolicy, Statement},
    transport::{ClusterData, ExecutionProfile, Node},
    LegacySession, SessionBuilder,
};
use std::{env, sync::Arc};

/// Example load balancing policy that prefers nodes from favorite datacenter
#[derive(Debug)]
struct CustomLoadBalancingPolicy {
    fav_datacenter_name: String,
}

impl LoadBalancingPolicy for CustomLoadBalancingPolicy {
    fn plan<'a>(
        &self,
        _statement: &Statement,
        cluster: &'a ClusterData,
    ) -> Box<dyn Iterator<Item = Arc<Node>> + Send + Sync + 'a> {
        let fav_dc_info = cluster
            .get_datacenters_info()
            .get(&self.fav_datacenter_name);

        match fav_dc_info {
            Some(info) => Box::new(info.nodes.iter().cloned()),
            // If there is no dc with provided name, fallback to other datacenters
            None => Box::new(cluster.get_nodes_info().iter().cloned()),
        }
    }

    fn name(&self) -> String {
        "CustomPolicy".to_string()
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let uri = env::var("SCYLLA_URI").unwrap_or_else(|_| "127.0.0.1:9042".to_string());

    let custom_load_balancing = CustomLoadBalancingPolicy {
        fav_datacenter_name: "PL".to_string(),
    };

    let profile = ExecutionProfile::builder()
        .load_balancing_policy(Arc::new(custom_load_balancing))
        .build();

    let _session: LegacySession = SessionBuilder::new()
        .known_node(uri)
        .default_execution_profile_handle(profile.into_handle())
        .build_legacy()
        .await?;

    Ok(())
}
