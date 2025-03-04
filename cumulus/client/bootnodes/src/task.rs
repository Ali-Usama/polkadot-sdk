// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Cumulus.

// Cumulus is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Cumulus is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Cumulus.  If not, see <http://www.gnu.org/licenses/>.

//! Parachain bootnodes advertisement and discovery service.

use crate::{
	advertisement::{BootnodeAdvertisement, BootnodeAdvertisementParams},
	discovery::{BootnodeDiscovery, BootnodeDiscoveryParams},
};
use cumulus_primitives_core::ParaId;
use cumulus_relay_chain_interface::RelayChainInterface;
use log::error;
use sc_network::{request_responses::IncomingRequest, service::traits::NetworkService, Multiaddr};
use sc_service::TaskManager;
use std::sync::Arc;

/// Log target for this crate.
const LOG_TARGET: &str = "bootnodes";

/// Bootnode advertisement task params.
pub struct StartBootnodeTasksParams<'a> {
	/// Parachain ID.
	pub para_id: ParaId,
	/// Task manager.
	pub task_manager: &'a mut TaskManager,
	/// Relay chain interface.
	pub relay_chain_interface: Arc<dyn RelayChainInterface>,
	/// `/paranode` protocol request receiver.
	pub request_receiver: async_channel::Receiver<IncomingRequest>,
	/// Parachain node network service.
	pub parachain_network: Arc<dyn NetworkService>,
	/// Whether to advertise non-global IP addresses.
	pub advertise_non_global_ips: bool,
	/// Parachain genesis hash.
	pub parachain_genesis_hash: Vec<u8>,
	/// Parachain fork ID.
	pub parachain_fork_id: Option<String>,
	/// Parachain public addresses provided by the operator.
	pub parachain_public_addresses: Vec<Multiaddr>,
}

async fn bootnode_advertisement(
	para_id: ParaId,
	relay_chain_interface: Arc<dyn RelayChainInterface>,
	request_receiver: async_channel::Receiver<IncomingRequest>,
	parachain_network: Arc<dyn NetworkService>,
	advertise_non_global_ips: bool,
	parachain_genesis_hash: Vec<u8>,
	parachain_fork_id: Option<String>,
	public_addresses: Vec<Multiaddr>,
) {
	let relay_chain_network = match relay_chain_interface.network_service() {
		Ok(network_service) => network_service,
		Err(e) => {
			error!(
				target: LOG_TARGET,
				"Bootnode advertisement: Failed to obtain network service: {e}",
			);
			// Returning here will cause an essential task to fail.
			return;
		},
	};

	let bootnode_advertisement = BootnodeAdvertisement::new(BootnodeAdvertisementParams {
		para_id,
		relay_chain_interface,
		relay_chain_network,
		request_receiver,
		parachain_network,
		advertise_non_global_ips,
		parachain_genesis_hash,
		parachain_fork_id,
		public_addresses,
	});

	if let Err(e) = bootnode_advertisement.run().await {
		error!(target: LOG_TARGET, "Bootnode advertisement terminated with error: {e}");
	}
}

async fn bootnode_discovery(
	para_id: ParaId,
	parachain_genesis_hash: Vec<u8>,
	parachain_fork_id: Option<String>,
	relay_chain_interface: Arc<dyn RelayChainInterface>,
) {
	let relay_chain_network = match relay_chain_interface.network_service() {
		Ok(network_service) => network_service,
		Err(e) => {
			error!(
				target: LOG_TARGET,
				"Bootnode discovery: Failed to obtain network service: {e}",
			);
			// Returning here will cause an essential task to fail.
			return;
		},
	};

	let bootnode_discovery = BootnodeDiscovery::new(BootnodeDiscoveryParams {
		para_id,
		parachain_genesis_hash,
		parachain_fork_id,
		relay_chain_network,
	});

	bootnode_discovery.run().await;
}

/// Start parachain bootnode advertisement and discovery tasks.
pub fn start_bootnode_tasks(
	StartBootnodeTasksParams {
		para_id,
		task_manager,
		relay_chain_interface,
		request_receiver,
		parachain_network,
		advertise_non_global_ips,
		parachain_genesis_hash,
		parachain_fork_id,
		parachain_public_addresses,
	}: StartBootnodeTasksParams,
) {
	task_manager.spawn_essential_handle().spawn(
		"cumulus-bootnode-advertisement",
		None,
		bootnode_advertisement(
			para_id,
			relay_chain_interface.clone(),
			request_receiver,
			parachain_network,
			advertise_non_global_ips,
			parachain_genesis_hash.clone(),
			parachain_fork_id.clone(),
			parachain_public_addresses,
		),
	);
	task_manager.spawn_essential_handle().spawn(
		"cumulus-bootnode-discovery",
		None,
		bootnode_discovery(
			para_id,
			parachain_genesis_hash,
			parachain_fork_id,
			relay_chain_interface,
		),
	);
}
