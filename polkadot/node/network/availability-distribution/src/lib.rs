// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use futures::{future::Either, FutureExt, StreamExt, TryFutureExt};

use sp_keystore::KeystorePtr;

use polkadot_node_network_protocol::request_response::{
	v1, v2, IncomingRequestReceiver, ReqProtocolNames,
};
use polkadot_node_subsystem::{
	messages::AvailabilityDistributionMessage, overseer, FromOrchestra, OverseerSignal,
	SpawnedSubsystem, SubsystemError,
};

/// Error and [`Result`] type for this subsystem.
mod error;
use error::{log_error, FatalError, Result};

use polkadot_node_subsystem_util::runtime::RuntimeInfo;

/// `Requester` taking care of requesting chunks for candidates pending availability.
mod requester;
use requester::Requester;

/// Handing requests for PoVs during backing.
mod pov_requester;

/// Responding to erasure chunk requests:
mod responder;
use responder::{run_chunk_receivers, run_pov_receiver};

mod metrics;
/// Prometheus `Metrics` for availability distribution.
pub use metrics::Metrics;

#[cfg(test)]
mod tests;

const LOG_TARGET: &'static str = "parachain::availability-distribution";

/// The availability distribution subsystem.
pub struct AvailabilityDistributionSubsystem {
	/// Easy and efficient runtime access for this subsystem.
	runtime: RuntimeInfo,
	/// Receivers to receive messages from.
	recvs: IncomingRequestReceivers,
	/// Mapping of the req-response protocols to the full protocol names.
	req_protocol_names: ReqProtocolNames,
	/// Prometheus metrics.
	metrics: Metrics,
}

/// Receivers to be passed into availability distribution.
pub struct IncomingRequestReceivers {
	/// Receiver for incoming PoV requests.
	pub pov_req_receiver: IncomingRequestReceiver<v1::PoVFetchingRequest>,
	/// Receiver for incoming v1 availability chunk requests.
	pub chunk_req_v1_receiver: IncomingRequestReceiver<v1::ChunkFetchingRequest>,
	/// Receiver for incoming v2 availability chunk requests.
	pub chunk_req_v2_receiver: IncomingRequestReceiver<v2::ChunkFetchingRequest>,
}

#[overseer::subsystem(AvailabilityDistribution, error=SubsystemError, prefix=self::overseer)]
impl<Context> AvailabilityDistributionSubsystem {
	fn start(self, ctx: Context) -> SpawnedSubsystem {
		let future = self
			.run(ctx)
			.map_err(|e| SubsystemError::with_origin("availability-distribution", e))
			.boxed();

		SpawnedSubsystem { name: "availability-distribution-subsystem", future }
	}
}

#[overseer::contextbounds(AvailabilityDistribution, prefix = self::overseer)]
impl AvailabilityDistributionSubsystem {
	/// Create a new instance of the availability distribution.
	pub fn new(
		keystore: KeystorePtr,
		recvs: IncomingRequestReceivers,
		req_protocol_names: ReqProtocolNames,
		metrics: Metrics,
	) -> Self {
		let runtime = RuntimeInfo::new(Some(keystore));
		Self { runtime, recvs, req_protocol_names, metrics }
	}

	/// Start processing work as passed on from the Overseer.
	async fn run<Context>(self, mut ctx: Context) -> std::result::Result<(), FatalError> {
		let Self { mut runtime, recvs, metrics, req_protocol_names } = self;

		let IncomingRequestReceivers {
			pov_req_receiver,
			chunk_req_v1_receiver,
			chunk_req_v2_receiver,
		} = recvs;
		let mut requester = Requester::new(req_protocol_names, metrics.clone()).fuse();
		let mut warn_freq = gum::Freq::new();

		{
			let sender = ctx.sender().clone();
			ctx.spawn(
				"pov-receiver",
				run_pov_receiver(sender.clone(), pov_req_receiver, metrics.clone()).boxed(),
			)
			.map_err(FatalError::SpawnTask)?;

			ctx.spawn(
				"chunk-receiver",
				run_chunk_receivers(
					sender,
					chunk_req_v1_receiver,
					chunk_req_v2_receiver,
					metrics.clone(),
				)
				.boxed(),
			)
			.map_err(FatalError::SpawnTask)?;
		}

		loop {
			let action = {
				let mut subsystem_next = ctx.recv().fuse();
				futures::select! {
					subsystem_msg = subsystem_next => Either::Left(subsystem_msg),
					from_task = requester.next() => Either::Right(from_task),
				}
			};

			// Handle task messages sending:
			let message = match action {
				Either::Left(subsystem_msg) => {
					subsystem_msg.map_err(|e| FatalError::IncomingMessageChannel(e))?
				},
				Either::Right(from_task) => {
					let from_task = from_task.ok_or(FatalError::RequesterExhausted)?;
					ctx.send_message(from_task).await;
					continue;
				},
			};
			match message {
				FromOrchestra::Signal(OverseerSignal::ActiveLeaves(update)) => {
					log_error(
						requester
							.get_mut()
							.update_fetching_heads(&mut ctx, &mut runtime, update)
							.await,
						"Error in Requester::update_fetching_heads",
						&mut warn_freq,
					)?;
				},
				FromOrchestra::Signal(OverseerSignal::BlockFinalized(_hash, _finalized_number)) => {
				},
				FromOrchestra::Signal(OverseerSignal::Conclude) => return Ok(()),
				FromOrchestra::Communication {
					msg:
						AvailabilityDistributionMessage::FetchPoV {
							relay_parent,
							from_validator,
							para_id,
							candidate_hash,
							pov_hash,
							tx,
						},
				} => {
					log_error(
						pov_requester::fetch_pov(
							&mut ctx,
							&mut runtime,
							relay_parent,
							from_validator,
							para_id,
							candidate_hash,
							pov_hash,
							tx,
							metrics.clone(),
						)
						.await,
						"pov_requester::fetch_pov",
						&mut warn_freq,
					)?;
				},
			}
		}
	}
}
