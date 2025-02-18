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


//! Autogenerated weights for `pallet_election_provider_multi_block::signed`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-18, STEPS: `2`, REPEAT: `3`, LOW RANGE: `[]`, HIGH RANGE: `[]`
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
// pallet_election_provider_multi_block::signed
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

/// Weight functions needed for `pallet_election_provider_multi_block::signed`.
pub trait WeightInfo {
	fn register_not_full() -> Weight;
	fn register_eject() -> Weight;
	fn submit_page() -> Weight;
	fn unset_page() -> Weight;
	fn bail() -> Weight;
}

/// Weights for `pallet_election_provider_multi_block::signed` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:0 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	fn register_not_full() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3043`
		//  Estimated: `4118`
		// Minimum execution time: 60_863_000 picoseconds.
		Weight::from_parts(61_253_000, 4118)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:2 w:2)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:2)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:32 w:32)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `MaxEncodedLen`)
	fn register_eject() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7643`
		//  Estimated: `1185054`
		// Minimum execution time: 149_097_000 picoseconds.
		Weight::from_parts(150_648_000, 1185054)
			.saturating_add(T::DbWeight::get().reads(38_u64))
			.saturating_add(T::DbWeight::get().writes(37_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `MaxEncodedLen`)
	fn submit_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3459`
		//  Estimated: `37992`
		// Minimum execution time: 132_381_000 picoseconds.
		Weight::from_parts(140_063_000, 37992)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `MaxEncodedLen`)
	fn unset_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4287`
		//  Estimated: `37992`
		// Minimum execution time: 124_078_000 picoseconds.
		Weight::from_parts(132_691_000, 37992)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:32 w:32)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	fn bail() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4508`
		//  Estimated: `1185054`
		// Minimum execution time: 115_736_000 picoseconds.
		Weight::from_parts(118_419_000, 1185054)
			.saturating_add(T::DbWeight::get().reads(37_u64))
			.saturating_add(T::DbWeight::get().writes(35_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:0 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	fn register_not_full() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3043`
		//  Estimated: `4118`
		// Minimum execution time: 60_863_000 picoseconds.
		Weight::from_parts(61_253_000, 4118)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:2 w:2)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:2)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:32 w:32)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `MaxEncodedLen`)
	fn register_eject() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7643`
		//  Estimated: `1185054`
		// Minimum execution time: 149_097_000 picoseconds.
		Weight::from_parts(150_648_000, 1185054)
			.saturating_add(RocksDbWeight::get().reads(38_u64))
			.saturating_add(RocksDbWeight::get().writes(37_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `MaxEncodedLen`)
	fn submit_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3459`
		//  Estimated: `37992`
		// Minimum execution time: 132_381_000 picoseconds.
		Weight::from_parts(140_063_000, 37992)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `MaxEncodedLen`)
	fn unset_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4287`
		//  Estimated: `37992`
		// Minimum execution time: 124_078_000 picoseconds.
		Weight::from_parts(132_691_000, 37992)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:32 w:32)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	fn bail() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4508`
		//  Estimated: `1185054`
		// Minimum execution time: 115_736_000 picoseconds.
		Weight::from_parts(118_419_000, 1185054)
			.saturating_add(RocksDbWeight::get().reads(37_u64))
			.saturating_add(RocksDbWeight::get().writes(35_u64))
	}
}
