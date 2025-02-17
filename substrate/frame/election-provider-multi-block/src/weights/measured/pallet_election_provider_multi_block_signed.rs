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
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:0 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	fn register_not_full() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3043`
		//  Estimated: `6508`
		// Minimum execution time: 62_425_000 picoseconds.
		Weight::from_parts(63_507_000, 6508)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:2 w:2)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:2)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:32 w:32)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `Measured`)
	fn register_eject() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7643`
		//  Estimated: `87833`
		// Minimum execution time: 148_826_000 picoseconds.
		Weight::from_parts(155_275_000, 87833)
			.saturating_add(T::DbWeight::get().reads(38_u64))
			.saturating_add(T::DbWeight::get().writes(37_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `Measured`)
	fn submit_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3459`
		//  Estimated: `6924`
		// Minimum execution time: 697_450_000 picoseconds.
		Weight::from_parts(762_938_000, 6924)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `Measured`)
	fn unset_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4287`
		//  Estimated: `7752`
		// Minimum execution time: 681_035_000 picoseconds.
		Weight::from_parts(711_671_000, 7752)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:32 w:32)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	fn bail() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4508`
		//  Estimated: `84698`
		// Minimum execution time: 117_619_000 picoseconds.
		Weight::from_parts(118_169_000, 84698)
			.saturating_add(T::DbWeight::get().reads(37_u64))
			.saturating_add(T::DbWeight::get().writes(35_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:0 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	fn register_not_full() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3043`
		//  Estimated: `6508`
		// Minimum execution time: 62_425_000 picoseconds.
		Weight::from_parts(63_507_000, 6508)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:2 w:2)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:2)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:32 w:32)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `Measured`)
	fn register_eject() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7643`
		//  Estimated: `87833`
		// Minimum execution time: 148_826_000 picoseconds.
		Weight::from_parts(155_275_000, 87833)
			.saturating_add(RocksDbWeight::get().reads(38_u64))
			.saturating_add(RocksDbWeight::get().writes(37_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `Measured`)
	fn submit_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3459`
		//  Estimated: `6924`
		// Minimum execution time: 697_450_000 picoseconds.
		Weight::from_parts(762_938_000, 6924)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `Measured`)
	fn unset_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4287`
		//  Estimated: `7752`
		// Minimum execution time: 681_035_000 picoseconds.
		Weight::from_parts(711_671_000, 7752)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: `MultiBlock::CurrentPhase` (r:1 w:0)
	/// Proof: `MultiBlock::CurrentPhase` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `Measured`)
	/// Storage: `MultiBlock::Round` (r:1 w:0)
	/// Proof: `MultiBlock::Round` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SortedScores` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SortedScores` (`max_values`: None, `max_size`: Some(653), added: 3128, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionStorage` (r:32 w:32)
	/// Proof: `MultiBlockSigned::SubmissionStorage` (`max_values`: None, `max_size`: Some(34527), added: 37002, mode: `Measured`)
	/// Storage: `MultiBlockSigned::SubmissionMetadataStorage` (r:1 w:1)
	/// Proof: `MultiBlockSigned::SubmissionMetadataStorage` (`max_values`: None, `max_size`: Some(181), added: 2656, mode: `Measured`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `Measured`)
	fn bail() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4508`
		//  Estimated: `84698`
		// Minimum execution time: 117_619_000 picoseconds.
		Weight::from_parts(118_169_000, 84698)
			.saturating_add(RocksDbWeight::get().reads(37_u64))
			.saturating_add(RocksDbWeight::get().writes(35_u64))
	}
}
