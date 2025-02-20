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

//! Autogenerated weights for `pallet_election_provider_multi_block::unsigned`
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
// pallet_election_provider_multi_block::unsigned
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
// --output
// ../mel

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]
#![allow(dead_code)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for `pallet_election_provider_multi_block::unsigned`.
pub trait WeightInfo {
	fn validate_unsigned() -> Weight;
	fn submit_unsigned() -> Weight;
}

/// Weights for `pallet_election_provider_multi_block::unsigned` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::QueuedSolutionScore` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::QueuedSolutionScore` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::MinimumScore` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::MinimumScore` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::DesiredTargets` (r:1 w:0)
	/// Proof: `MultiBlock::DesiredTargets` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn validate_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `364`
		//  Estimated: `1533`
		// Minimum execution time: 77_037_000 picoseconds.
		Weight::from_parts(77_588_000, 1533)
			.saturating_add(T::DbWeight::get().reads(5_u64))
	}
	/// Storage: `MultiBlockVerifier::QueuedSolutionScore` (r:1 w:1)
	/// Proof: `MultiBlockVerifier::QueuedSolutionScore` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::MinimumScore` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::MinimumScore` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::PagedTargetSnapshot` (r:1 w:0)
	/// Proof: `MultiBlock::PagedTargetSnapshot` (`max_values`: None, `max_size`: Some(32014), added: 34489, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::PagedVoterSnapshot` (r:1 w:0)
	/// Proof: `MultiBlock::PagedVoterSnapshot` (`max_values`: None, `max_size`: Some(388773), added: 391248, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::DesiredTargets` (r:1 w:0)
	/// Proof: `MultiBlock::DesiredTargets` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::QueuedValidVariant` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::QueuedValidVariant` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::QueuedSolutionY` (r:0 w:1)
	/// Proof: `MultiBlockVerifier::QueuedSolutionY` (`max_values`: None, `max_size`: Some(6194014), added: 6196489, mode: `MaxEncodedLen`)
	fn submit_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `157641`
		//  Estimated: `392238`
		// Minimum execution time: 3_607_268_000 picoseconds.
		Weight::from_parts(4_015_058_000, 392238)
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::QueuedSolutionScore` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::QueuedSolutionScore` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::MinimumScore` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::MinimumScore` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::DesiredTargets` (r:1 w:0)
	/// Proof: `MultiBlock::DesiredTargets` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn validate_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `364`
		//  Estimated: `1533`
		// Minimum execution time: 77_037_000 picoseconds.
		Weight::from_parts(77_588_000, 1533)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
	}
	/// Storage: `MultiBlockVerifier::QueuedSolutionScore` (r:1 w:1)
	/// Proof: `MultiBlockVerifier::QueuedSolutionScore` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::MinimumScore` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::MinimumScore` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::PagedTargetSnapshot` (r:1 w:0)
	/// Proof: `MultiBlock::PagedTargetSnapshot` (`max_values`: None, `max_size`: Some(32014), added: 34489, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::PagedVoterSnapshot` (r:1 w:0)
	/// Proof: `MultiBlock::PagedVoterSnapshot` (`max_values`: None, `max_size`: Some(388773), added: 391248, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::DesiredTargets` (r:1 w:0)
	/// Proof: `MultiBlock::DesiredTargets` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::QueuedValidVariant` (r:1 w:0)
	/// Proof: `MultiBlockVerifier::QueuedValidVariant` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockVerifier::QueuedSolutionY` (r:0 w:1)
	/// Proof: `MultiBlockVerifier::QueuedSolutionY` (`max_values`: None, `max_size`: Some(6194014), added: 6196489, mode: `MaxEncodedLen`)
	fn submit_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `157641`
		//  Estimated: `392238`
		// Minimum execution time: 3_607_268_000 picoseconds.
		Weight::from_parts(4_015_058_000, 392238)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
}
