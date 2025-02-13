// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

use anyhow::anyhow;
use codec::Decode;
use polkadot_primitives::{vstaging::CandidateReceiptV2, Id as ParaId};
use std::{collections::HashMap, ops::Range};
use subxt::{
	events::Events, ext::scale_value::value, tx::DynamicPayload, utils::H256, OnlineClient,
	PolkadotConfig,
};

/// Create a batch call to assign cores to a parachain.
pub fn create_assign_core_call(cores: &[u32], para_id: u32) -> DynamicPayload {
	let mut assign_cores = vec![];
	for core in cores.iter() {
		assign_cores.push(value! {
			Coretime(assign_core { core : *core, begin: 0, assignment: ((Task(para_id), 57600)), end_hint: None() })
		});
	}

	subxt::tx::dynamic(
		"Sudo",
		"sudo",
		vec![value! {
			Utility(batch { calls: assign_cores })
		}],
	)
}

/// Find an event in subxt `Events` and attempt to decode the fields fo the event.
fn find_event_and_decode_fields<T: Decode>(
	events: &Events<PolkadotConfig>,
	pallet: &str,
	variant: &str,
) -> Result<Vec<T>, anyhow::Error> {
	let mut result = vec![];
	for event in events.iter() {
		let event = event?;
		if event.pallet_name() == pallet && event.variant_name() == variant {
			let field_bytes = event.field_bytes().to_vec();
			result.push(T::decode(&mut &field_bytes[..])?);
		}
	}
	Ok(result)
}

// Helper function for asserting the throughput of parachains (total number of backed candidates in
// a window of relay chain blocks), after the first session change.
pub async fn assert_para_throughput(
	relay_client: &OnlineClient<PolkadotConfig>,
	stop_at: u32,
	expected_candidate_ranges: HashMap<ParaId, Range<u32>>,
) -> Result<(), anyhow::Error> {
	let mut blocks_sub = relay_client.blocks().subscribe_finalized().await?;
	let mut candidate_count: HashMap<ParaId, u32> = HashMap::new();
	let mut current_block_count = 0;
	let mut had_first_session_change = false;
	let valid_para_ids: Vec<ParaId> = expected_candidate_ranges.keys().cloned().collect();

	while let Some(block) = blocks_sub.next().await {
		let block = block?;
		log::debug!("Finalized relay chain block {}", block.number());
		let events = block.events().await?;
		let is_session_change = events
			.iter()
			.find(|event| {
				event.as_ref().is_ok_and(|event| {
					event.pallet_name() == "Session" && event.variant_name() == "NewSession"
				})
			})
			.is_some();

		if !had_first_session_change && is_session_change {
			had_first_session_change = true;
		}

		if had_first_session_change && !is_session_change {
			current_block_count += 1;

			let receipts = find_event_and_decode_fields::<CandidateReceiptV2<H256>>(
				&events,
				"ParaInclusion",
				"CandidateBacked",
			)?;

			for receipt in receipts {
				let para_id = receipt.descriptor.para_id();
				log::debug!("Block backed for para_id {para_id}");
				if !valid_para_ids.contains(&para_id) {
					return Err(anyhow!("Invalid ParaId detected: {}", para_id));
				};
				*(candidate_count.entry(para_id).or_default()) += 1;
			}
		}

		if current_block_count == stop_at {
			break;
		}
	}

	log::info!(
		"Reached {} finalized relay chain blocks that contain backed candidates. The per-parachain distribution is: {:#?}",
		stop_at,
		candidate_count
	);

	for (para_id, expected_candidate_range) in expected_candidate_ranges {
		let actual = candidate_count
			.get(&para_id)
			.expect("ParaId did not have any backed candidates");
		assert!(
			expected_candidate_range.contains(actual),
			"Candidate count {actual} not within range {expected_candidate_range:?}"
		);
	}

	Ok(())
}

// Helper function for retrieving the latest finalized block height and asserting it's within a
// range.
pub async fn assert_finalized_block_height(
	client: &OnlineClient<PolkadotConfig>,
	expected_range: Range<u32>,
) -> Result<(), anyhow::Error> {
	if let Some(block) = client.blocks().subscribe_finalized().await?.next().await {
		let height = block?.number();
		log::info!("Finalized block number {height}");

		assert!(
			expected_range.contains(&height),
			"Finalized block number {height} not within range {expected_range:?}"
		);
	}
	Ok(())
}
