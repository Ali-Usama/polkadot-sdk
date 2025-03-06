// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Autogenerated weights for `pallet_election_provider_multi_block`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-13, STEPS: `2`, REPEAT: `3`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `toaster1`, CPU: `AMD Ryzen Threadripper 7980X 64-Cores`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("dev")`, DB CACHE: `1024`

// Executed Command:
// target/release/substrate-node
// benchmark
// pallet
// --chain
// dev
// --pallet
// pallet_election_provider_multi_block
// --extrinsic
// all
// --steps
// 2
// --repeat
// 3
// --template
// substrate/.maintain/frame-weight-template.hbs
// --heap-pages
// 65000
// --default-pov-mode
// measured
// --output
// ../measured

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]
#![allow(dead_code)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for `pallet_election_provider_multi_block`.
pub trait WeightInfo {
	fn on_initialize_nothing() -> Weight;
	fn on_initialize_into_snapshot_msp() -> Weight;
	fn on_initialize_into_snapshot_rest() -> Weight;
	fn on_initialize_into_signed() -> Weight;
	fn on_initialize_into_signed_validation() -> Weight;
	fn on_initialize_into_unsigned() -> Weight;
	fn manage() -> Weight;
}

/// Weights for `pallet_election_provider_multi_block` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	fn on_initialize_nothing() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `156`
		//  Estimated: `1641`
		// Minimum execution time: 9_254_000 picoseconds.
		Weight::from_parts(10_145_000, 1641)
			.saturating_add(T::DbWeight::get().reads(2_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `Staking::ValidatorCount` (r:1 w:0)
	/// Proof: `Staking::ValidatorCount` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `Staking::CounterForValidators` (r:1 w:0)
	/// Proof: `Staking::CounterForValidators` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `Staking::Validators` (r:1002 w:0)
	/// Proof: `Staking::Validators` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `Measured`)
	/// Storage: `Staking::VoterSnapshotStatus` (r:1 w:1)
	/// Proof: `Staking::VoterSnapshotStatus` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `Measured`)
	/// Storage: `VoterList::CounterForListNodes` (r:1 w:0)
	/// Proof: `VoterList::CounterForListNodes` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `VoterList::ListBags` (r:200 w:0)
	/// Proof: `VoterList::ListBags` (`max_values`: None, `max_size`: Some(82), added: 2557, mode: `Measured`)
	/// Storage: `VoterList::ListNodes` (r:26001 w:0)
	/// Proof: `VoterList::ListNodes` (`max_values`: None, `max_size`: Some(154), added: 2629, mode: `Measured`)
	/// Storage: `Staking::Bonded` (r:703 w:0)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `Measured`)
	/// Storage: `Staking::Ledger` (r:703 w:0)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `Measured`)
	/// Storage: `Staking::Nominators` (r:703 w:0)
	/// Proof: `Staking::Nominators` (`max_values`: None, `max_size`: Some(558), added: 3033, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::PagedVoterSnapshot` (r:0 w:1)
	/// Proof: `MultiBlock::PagedVoterSnapshot` (`max_values`: None, `max_size`: Some(388773), added: 391248, mode: `Measured`)
	/// Storage: `MultiBlock::DesiredTargets` (r:0 w:1)
	/// Proof: `MultiBlock::DesiredTargets` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlock::PagedTargetSnapshotHash` (r:0 w:1)
	/// Proof: `MultiBlock::PagedTargetSnapshotHash` (`max_values`: None, `max_size`: Some(44), added: 2519, mode: `Measured`)
	/// Storage: `MultiBlock::PagedTargetSnapshot` (r:0 w:1)
	/// Proof: `MultiBlock::PagedTargetSnapshot` (`max_values`: None, `max_size`: Some(32014), added: 34489, mode: `Measured`)
	/// Storage: `MultiBlock::PagedVoterSnapshotHash` (r:0 w:1)
	/// Proof: `MultiBlock::PagedVoterSnapshotHash` (`max_values`: None, `max_size`: Some(44), added: 2519, mode: `Measured`)
	/// Storage: `Staking::MinimumActiveStake` (r:0 w:1)
	/// Proof: `Staking::MinimumActiveStake` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `Measured`)
	fn on_initialize_into_snapshot_msp() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `5151586`
		//  Estimated: `69505051`
		// Minimum execution time: 201_905_061_000 picoseconds.
		Weight::from_parts(203_148_720_000, 69505051)
			.saturating_add(T::DbWeight::get().reads(29318_u64))
			.saturating_add(T::DbWeight::get().writes(8_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `Staking::VoterSnapshotStatus` (r:1 w:1)
	/// Proof: `Staking::VoterSnapshotStatus` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `Measured`)
	/// Storage: `VoterList::CounterForListNodes` (r:1 w:0)
	/// Proof: `VoterList::CounterForListNodes` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `VoterList::ListNodes` (r:26001 w:0)
	/// Proof: `VoterList::ListNodes` (`max_values`: None, `max_size`: Some(154), added: 2629, mode: `Measured`)
	/// Storage: `Staking::Bonded` (r:704 w:0)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `Measured`)
	/// Storage: `Staking::Ledger` (r:704 w:0)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `Measured`)
	/// Storage: `Staking::Nominators` (r:703 w:0)
	/// Proof: `Staking::Nominators` (`max_values`: None, `max_size`: Some(558), added: 3033, mode: `Measured`)
	/// Storage: `VoterList::ListBags` (r:200 w:0)
	/// Proof: `VoterList::ListBags` (`max_values`: None, `max_size`: Some(82), added: 2557, mode: `Measured`)
	/// Storage: `Staking::Validators` (r:165 w:0)
	/// Proof: `Staking::Validators` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::PagedVoterSnapshot` (r:0 w:1)
	/// Proof: `MultiBlock::PagedVoterSnapshot` (`max_values`: None, `max_size`: Some(388773), added: 391248, mode: `Measured`)
	/// Storage: `MultiBlock::PagedVoterSnapshotHash` (r:0 w:1)
	/// Proof: `MultiBlock::PagedVoterSnapshotHash` (`max_values`: None, `max_size`: Some(44), added: 2519, mode: `Measured`)
	/// Storage: `Staking::MinimumActiveStake` (r:0 w:1)
	/// Proof: `Staking::MinimumActiveStake` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `Measured`)
	fn on_initialize_into_snapshot_rest() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `5329975`
		//  Estimated: `69683440`
		// Minimum execution time: 195_257_628_000 picoseconds.
		Weight::from_parts(195_317_909_000, 69683440)
			.saturating_add(T::DbWeight::get().reads(28481_u64))
			.saturating_add(T::DbWeight::get().writes(5_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	fn on_initialize_into_signed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `340`
		//  Estimated: `1825`
		// Minimum execution time: 649_767_000 picoseconds.
		Weight::from_parts(764_370_000, 1825)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:0)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `Measured`)
	fn on_initialize_into_signed_validation() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `340`
		//  Estimated: `3805`
		// Minimum execution time: 657_218_000 picoseconds.
		Weight::from_parts(674_575_000, 3805)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:1)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::QueuedValidVariant` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::QueuedValidVariant` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `Measured`)
	fn on_initialize_into_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `340`
		//  Estimated: `1825`
		// Minimum execution time: 866_827_000 picoseconds.
		Weight::from_parts(890_863_000, 1825)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	fn manage() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 140_000 picoseconds.
		Weight::from_parts(170_000, 0)
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	fn on_initialize_nothing() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `156`
		//  Estimated: `1641`
		// Minimum execution time: 9_254_000 picoseconds.
		Weight::from_parts(10_145_000, 1641)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `Staking::ValidatorCount` (r:1 w:0)
	/// Proof: `Staking::ValidatorCount` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `Staking::CounterForValidators` (r:1 w:0)
	/// Proof: `Staking::CounterForValidators` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `Staking::Validators` (r:1002 w:0)
	/// Proof: `Staking::Validators` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `Measured`)
	/// Storage: `Staking::VoterSnapshotStatus` (r:1 w:1)
	/// Proof: `Staking::VoterSnapshotStatus` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `Measured`)
	/// Storage: `VoterList::CounterForListNodes` (r:1 w:0)
	/// Proof: `VoterList::CounterForListNodes` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `VoterList::ListBags` (r:200 w:0)
	/// Proof: `VoterList::ListBags` (`max_values`: None, `max_size`: Some(82), added: 2557, mode: `Measured`)
	/// Storage: `VoterList::ListNodes` (r:26001 w:0)
	/// Proof: `VoterList::ListNodes` (`max_values`: None, `max_size`: Some(154), added: 2629, mode: `Measured`)
	/// Storage: `Staking::Bonded` (r:703 w:0)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `Measured`)
	/// Storage: `Staking::Ledger` (r:703 w:0)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `Measured`)
	/// Storage: `Staking::Nominators` (r:703 w:0)
	/// Proof: `Staking::Nominators` (`max_values`: None, `max_size`: Some(558), added: 3033, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::PagedVoterSnapshot` (r:0 w:1)
	/// Proof: `MultiBlock::PagedVoterSnapshot` (`max_values`: None, `max_size`: Some(388773), added: 391248, mode: `Measured`)
	/// Storage: `MultiBlock::DesiredTargets` (r:0 w:1)
	/// Proof: `MultiBlock::DesiredTargets` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlock::PagedTargetSnapshotHash` (r:0 w:1)
	/// Proof: `MultiBlock::PagedTargetSnapshotHash` (`max_values`: None, `max_size`: Some(44), added: 2519, mode: `Measured`)
	/// Storage: `MultiBlock::PagedTargetSnapshot` (r:0 w:1)
	/// Proof: `MultiBlock::PagedTargetSnapshot` (`max_values`: None, `max_size`: Some(32014), added: 34489, mode: `Measured`)
	/// Storage: `MultiBlock::PagedVoterSnapshotHash` (r:0 w:1)
	/// Proof: `MultiBlock::PagedVoterSnapshotHash` (`max_values`: None, `max_size`: Some(44), added: 2519, mode: `Measured`)
	/// Storage: `Staking::MinimumActiveStake` (r:0 w:1)
	/// Proof: `Staking::MinimumActiveStake` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `Measured`)
	fn on_initialize_into_snapshot_msp() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `5151586`
		//  Estimated: `69505051`
		// Minimum execution time: 201_905_061_000 picoseconds.
		Weight::from_parts(203_148_720_000, 69505051)
			.saturating_add(RocksDbWeight::get().reads(29318_u64))
			.saturating_add(RocksDbWeight::get().writes(8_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `Staking::VoterSnapshotStatus` (r:1 w:1)
	/// Proof: `Staking::VoterSnapshotStatus` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `Measured`)
	/// Storage: `VoterList::CounterForListNodes` (r:1 w:0)
	/// Proof: `VoterList::CounterForListNodes` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `VoterList::ListNodes` (r:26001 w:0)
	/// Proof: `VoterList::ListNodes` (`max_values`: None, `max_size`: Some(154), added: 2629, mode: `Measured`)
	/// Storage: `Staking::Bonded` (r:704 w:0)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `Measured`)
	/// Storage: `Staking::Ledger` (r:704 w:0)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `Measured`)
	/// Storage: `Staking::Nominators` (r:703 w:0)
	/// Proof: `Staking::Nominators` (`max_values`: None, `max_size`: Some(558), added: 3033, mode: `Measured`)
	/// Storage: `VoterList::ListBags` (r:200 w:0)
	/// Proof: `VoterList::ListBags` (`max_values`: None, `max_size`: Some(82), added: 2557, mode: `Measured`)
	/// Storage: `Staking::Validators` (r:165 w:0)
	/// Proof: `Staking::Validators` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::PagedVoterSnapshot` (r:0 w:1)
	/// Proof: `MultiBlock::PagedVoterSnapshot` (`max_values`: None, `max_size`: Some(388773), added: 391248, mode: `Measured`)
	/// Storage: `MultiBlock::PagedVoterSnapshotHash` (r:0 w:1)
	/// Proof: `MultiBlock::PagedVoterSnapshotHash` (`max_values`: None, `max_size`: Some(44), added: 2519, mode: `Measured`)
	/// Storage: `Staking::MinimumActiveStake` (r:0 w:1)
	/// Proof: `Staking::MinimumActiveStake` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `Measured`)
	fn on_initialize_into_snapshot_rest() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `5329975`
		//  Estimated: `69683440`
		// Minimum execution time: 195_257_628_000 picoseconds.
		Weight::from_parts(195_317_909_000, 69683440)
			.saturating_add(RocksDbWeight::get().reads(28481_u64))
			.saturating_add(RocksDbWeight::get().writes(5_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	fn on_initialize_into_signed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `340`
		//  Estimated: `1825`
		// Minimum execution time: 649_767_000 picoseconds.
		Weight::from_parts(764_370_000, 1825)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:0)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `Measured`)
	fn on_initialize_into_signed_validation() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `340`
		//  Estimated: `3805`
		// Minimum execution time: 657_218_000 picoseconds.
		Weight::from_parts(674_575_000, 3805)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:1)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::StatusStorage` (r:1 w:1)
	/// Proof: `MultiBlockVerifier::StatusStorage` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlockVerifier::QueuedValidVariant` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::QueuedValidVariant` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `Measured`)
	fn on_initialize_into_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `340`
		//  Estimated: `1825`
		// Minimum execution time: 866_827_000 picoseconds.
		Weight::from_parts(890_863_000, 1825)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	fn manage() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 140_000 picoseconds.
		Weight::from_parts(170_000, 0)
	}
}
