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

//! Autogenerated weights for `pallet_ranked_collective`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `b4e4da69142b`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("dev")`, DB CACHE: `1024`

// Executed Command:
// target/production/substrate-node
// benchmark
// pallet
// --extrinsic=*
// --chain=dev
// --pallet=pallet_ranked_collective
// --header=/__w/polkadot-sdk/polkadot-sdk/substrate/HEADER-APACHE2
// --output=/__w/polkadot-sdk/polkadot-sdk/substrate/frame/ranked-collective/src/weights.rs
// --wasm-execution=compiled
// --steps=50
// --repeat=20
// --heap-pages=4096
// --template=substrate/.maintain/frame-weight-template.hbs
// --no-storage-info
// --no-min-squares
// --no-median-slopes

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame::weights_prelude::*;

/// Weight functions needed for `pallet_ranked_collective`.
pub trait WeightInfo {
	fn add_member() -> Weight;
	fn remove_member(r: u32, ) -> Weight;
	fn promote_member(r: u32, ) -> Weight;
	fn demote_member(r: u32, ) -> Weight;
	fn vote() -> Weight;
	fn cleanup_poll(n: u32, ) -> Weight;
	fn exchange_member() -> Weight;
}

/// Weights for `pallet_ranked_collective` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `RankedCollective::Members` (r:1 w:1)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:1 w:1)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:0 w:1)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:0 w:1)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	fn add_member() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `142`
		//  Estimated: `3507`
		// Minimum execution time: 16_319_000 picoseconds.
		Weight::from_parts(16_532_000, 3507)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(4_u64))
	}
	/// Storage: `RankedCollective::Members` (r:1 w:1)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:11 w:11)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:11 w:22)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:11 w:22)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[0, 10]`.
	fn remove_member(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `514 + r * (213 ±0)`
		//  Estimated: `3519 + r * (2529 ±0)`
		// Minimum execution time: 36_800_000 picoseconds.
		Weight::from_parts(38_084_412, 3519)
			// Standard Error: 46_319
			.saturating_add(Weight::from_parts(18_018_619, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().reads((3_u64).saturating_mul(r.into())))
			.saturating_add(T::DbWeight::get().writes(6_u64))
			.saturating_add(T::DbWeight::get().writes((5_u64).saturating_mul(r.into())))
			.saturating_add(Weight::from_parts(0, 2529).saturating_mul(r.into()))
	}
	/// Storage: `RankedCollective::Members` (r:1 w:1)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:1 w:1)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:0 w:1)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:0 w:1)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[0, 10]`.
	fn promote_member(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `314 + r * (17 ±0)`
		//  Estimated: `3507`
		// Minimum execution time: 20_063_000 picoseconds.
		Weight::from_parts(21_385_345, 3507)
			// Standard Error: 5_973
			.saturating_add(Weight::from_parts(411_940, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(4_u64))
	}
	/// Storage: `RankedCollective::Members` (r:1 w:1)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:1 w:1)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:1 w:2)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:1 w:2)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[0, 10]`.
	fn demote_member(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `530 + r * (72 ±0)`
		//  Estimated: `3519`
		// Minimum execution time: 36_852_000 picoseconds.
		Weight::from_parts(40_342_579, 3519)
			// Standard Error: 26_009
			.saturating_add(Weight::from_parts(812_780, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: `RankedCollective::Members` (r:1 w:0)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedPolls::ReferendumInfoFor` (r:1 w:1)
	/// Proof: `RankedPolls::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(330), added: 2805, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::Voting` (r:1 w:1)
	/// Proof: `RankedCollective::Voting` (`max_values`: None, `max_size`: Some(65), added: 2540, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Agenda` (r:2 w:2)
	/// Proof: `Scheduler::Agenda` (`max_values`: None, `max_size`: Some(107022), added: 109497, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Retries` (r:0 w:1)
	/// Proof: `Scheduler::Retries` (`max_values`: None, `max_size`: Some(30), added: 2505, mode: `MaxEncodedLen`)
	fn vote() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `580`
		//  Estimated: `219984`
		// Minimum execution time: 47_741_000 picoseconds.
		Weight::from_parts(49_723_000, 219984)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(5_u64))
	}
	/// Storage: `RankedPolls::ReferendumInfoFor` (r:1 w:0)
	/// Proof: `RankedPolls::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(330), added: 2805, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::VotingCleanup` (r:1 w:0)
	/// Proof: `RankedCollective::VotingCleanup` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::Voting` (r:100 w:100)
	/// Proof: `RankedCollective::Voting` (`max_values`: None, `max_size`: Some(65), added: 2540, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 100]`.
	fn cleanup_poll(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462 + n * (50 ±0)`
		//  Estimated: `3795 + n * (2540 ±0)`
		// Minimum execution time: 19_341_000 picoseconds.
		Weight::from_parts(24_113_657, 3795)
			// Standard Error: 3_187
			.saturating_add(Weight::from_parts(1_289_281, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(n.into())))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(n.into())))
			.saturating_add(Weight::from_parts(0, 2540).saturating_mul(n.into()))
	}
	/// Storage: `RankedCollective::Members` (r:2 w:2)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:2 w:2)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:2 w:4)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `CoreFellowship::Member` (r:2 w:2)
	/// Proof: `CoreFellowship::Member` (`max_values`: None, `max_size`: Some(49), added: 2524, mode: `MaxEncodedLen`)
	/// Storage: `CoreFellowship::MemberEvidence` (r:1 w:0)
	/// Proof: `CoreFellowship::MemberEvidence` (`max_values`: None, `max_size`: Some(16429), added: 18904, mode: `MaxEncodedLen`)
	/// Storage: `Salary::Claimant` (r:2 w:2)
	/// Proof: `Salary::Claimant` (`max_values`: None, `max_size`: Some(78), added: 2553, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:0 w:2)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	fn exchange_member() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `625`
		//  Estimated: `19894`
		// Minimum execution time: 79_259_000 picoseconds.
		Weight::from_parts(81_570_000, 19894)
			.saturating_add(T::DbWeight::get().reads(11_u64))
			.saturating_add(T::DbWeight::get().writes(14_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `RankedCollective::Members` (r:1 w:1)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:1 w:1)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:0 w:1)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:0 w:1)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	fn add_member() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `142`
		//  Estimated: `3507`
		// Minimum execution time: 16_319_000 picoseconds.
		Weight::from_parts(16_532_000, 3507)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
	}
	/// Storage: `RankedCollective::Members` (r:1 w:1)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:11 w:11)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:11 w:22)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:11 w:22)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[0, 10]`.
	fn remove_member(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `514 + r * (213 ±0)`
		//  Estimated: `3519 + r * (2529 ±0)`
		// Minimum execution time: 36_800_000 picoseconds.
		Weight::from_parts(38_084_412, 3519)
			// Standard Error: 46_319
			.saturating_add(Weight::from_parts(18_018_619, 0).saturating_mul(r.into()))
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().reads((3_u64).saturating_mul(r.into())))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
			.saturating_add(RocksDbWeight::get().writes((5_u64).saturating_mul(r.into())))
			.saturating_add(Weight::from_parts(0, 2529).saturating_mul(r.into()))
	}
	/// Storage: `RankedCollective::Members` (r:1 w:1)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:1 w:1)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:0 w:1)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:0 w:1)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[0, 10]`.
	fn promote_member(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `314 + r * (17 ±0)`
		//  Estimated: `3507`
		// Minimum execution time: 20_063_000 picoseconds.
		Weight::from_parts(21_385_345, 3507)
			// Standard Error: 5_973
			.saturating_add(Weight::from_parts(411_940, 0).saturating_mul(r.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
	}
	/// Storage: `RankedCollective::Members` (r:1 w:1)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:1 w:1)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:1 w:2)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:1 w:2)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[0, 10]`.
	fn demote_member(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `530 + r * (72 ±0)`
		//  Estimated: `3519`
		// Minimum execution time: 36_852_000 picoseconds.
		Weight::from_parts(40_342_579, 3519)
			// Standard Error: 26_009
			.saturating_add(Weight::from_parts(812_780, 0).saturating_mul(r.into()))
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: `RankedCollective::Members` (r:1 w:0)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedPolls::ReferendumInfoFor` (r:1 w:1)
	/// Proof: `RankedPolls::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(330), added: 2805, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::Voting` (r:1 w:1)
	/// Proof: `RankedCollective::Voting` (`max_values`: None, `max_size`: Some(65), added: 2540, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Agenda` (r:2 w:2)
	/// Proof: `Scheduler::Agenda` (`max_values`: None, `max_size`: Some(107022), added: 109497, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Retries` (r:0 w:1)
	/// Proof: `Scheduler::Retries` (`max_values`: None, `max_size`: Some(30), added: 2505, mode: `MaxEncodedLen`)
	fn vote() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `580`
		//  Estimated: `219984`
		// Minimum execution time: 47_741_000 picoseconds.
		Weight::from_parts(49_723_000, 219984)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(5_u64))
	}
	/// Storage: `RankedPolls::ReferendumInfoFor` (r:1 w:0)
	/// Proof: `RankedPolls::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(330), added: 2805, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::VotingCleanup` (r:1 w:0)
	/// Proof: `RankedCollective::VotingCleanup` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::Voting` (r:100 w:100)
	/// Proof: `RankedCollective::Voting` (`max_values`: None, `max_size`: Some(65), added: 2540, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 100]`.
	fn cleanup_poll(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462 + n * (50 ±0)`
		//  Estimated: `3795 + n * (2540 ±0)`
		// Minimum execution time: 19_341_000 picoseconds.
		Weight::from_parts(24_113_657, 3795)
			// Standard Error: 3_187
			.saturating_add(Weight::from_parts(1_289_281, 0).saturating_mul(n.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().reads((1_u64).saturating_mul(n.into())))
			.saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(n.into())))
			.saturating_add(Weight::from_parts(0, 2540).saturating_mul(n.into()))
	}
	/// Storage: `RankedCollective::Members` (r:2 w:2)
	/// Proof: `RankedCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::MemberCount` (r:2 w:2)
	/// Proof: `RankedCollective::MemberCount` (`max_values`: None, `max_size`: Some(14), added: 2489, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IdToIndex` (r:2 w:4)
	/// Proof: `RankedCollective::IdToIndex` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	/// Storage: `CoreFellowship::Member` (r:2 w:2)
	/// Proof: `CoreFellowship::Member` (`max_values`: None, `max_size`: Some(49), added: 2524, mode: `MaxEncodedLen`)
	/// Storage: `CoreFellowship::MemberEvidence` (r:1 w:0)
	/// Proof: `CoreFellowship::MemberEvidence` (`max_values`: None, `max_size`: Some(16429), added: 18904, mode: `MaxEncodedLen`)
	/// Storage: `Salary::Claimant` (r:2 w:2)
	/// Proof: `Salary::Claimant` (`max_values`: None, `max_size`: Some(78), added: 2553, mode: `MaxEncodedLen`)
	/// Storage: `RankedCollective::IndexToId` (r:0 w:2)
	/// Proof: `RankedCollective::IndexToId` (`max_values`: None, `max_size`: Some(54), added: 2529, mode: `MaxEncodedLen`)
	fn exchange_member() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `625`
		//  Estimated: `19894`
		// Minimum execution time: 79_259_000 picoseconds.
		Weight::from_parts(81_570_000, 19894)
			.saturating_add(RocksDbWeight::get().reads(11_u64))
			.saturating_add(RocksDbWeight::get().writes(14_u64))
	}
}
