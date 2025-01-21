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

//! Autogenerated weights for `pallet_child_bounties`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `92d5ef293533`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("dev")`, DB CACHE: `1024`

// Executed Command:
// target/production/substrate-node
// benchmark
// pallet
// --extrinsic=*
// --chain=dev
// --pallet=pallet_child_bounties
// --header=/__w/polkadot-sdk/polkadot-sdk/substrate/HEADER-APACHE2
// --output=/__w/polkadot-sdk/polkadot-sdk/substrate/frame/child-bounties/src/weights.rs
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

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for `pallet_child_bounties`.
pub trait WeightInfo {
	fn add_child_bounty(d: u32, ) -> Weight;
	fn propose_curator() -> Weight;
	fn accept_curator() -> Weight;
	fn unassign_curator() -> Weight;
	fn award_child_bounty() -> Weight;
	fn claim_child_bounty() -> Weight;
	fn close_child_bounty_added() -> Weight;
	fn close_child_bounty_active() -> Weight;
}

/// Weights for `pallet_child_bounties` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `ChildBounties::ParentChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ParentTotalChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentTotalChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBountyDescriptionsV1` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBountyDescriptionsV1` (`max_values`: None, `max_size`: Some(326), added: 2801, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// The range of component `d` is `[0, 300]`.
	fn add_child_bounty(d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `812`
		//  Estimated: `6196`
		// Minimum execution time: 71_931_000 picoseconds.
		Weight::from_parts(75_087_378, 6196)
			// Standard Error: 526
			.saturating_add(Weight::from_parts(668, 0).saturating_mul(d.into()))
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildrenCuratorFees` (r:1 w:1)
	/// Proof: `ChildBounties::ChildrenCuratorFees` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	fn propose_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `842`
		//  Estimated: `3642`
		// Minimum execution time: 25_376_000 picoseconds.
		Weight::from_parts(26_152_000, 3642)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn accept_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1048`
		//  Estimated: `3642`
		// Minimum execution time: 40_867_000 picoseconds.
		Weight::from_parts(41_955_000, 3642)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn unassign_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1048`
		//  Estimated: `3642`
		// Minimum execution time: 50_205_000 picoseconds.
		Weight::from_parts(52_117_000, 3642)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	fn award_child_bounty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `908`
		//  Estimated: `3642`
		// Minimum execution time: 27_062_000 picoseconds.
		Weight::from_parts(27_648_000, 3642)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:3 w:3)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ParentChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBountyDescriptionsV1` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBountyDescriptionsV1` (`max_values`: None, `max_size`: Some(326), added: 2801, mode: `MaxEncodedLen`)
	fn claim_child_bounty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `752`
		//  Estimated: `8799`
		// Minimum execution time: 111_020_000 picoseconds.
		Weight::from_parts(114_221_000, 8799)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildrenCuratorFees` (r:1 w:1)
	/// Proof: `ChildBounties::ChildrenCuratorFees` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ParentChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBountyDescriptionsV1` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBountyDescriptionsV1` (`max_values`: None, `max_size`: Some(326), added: 2801, mode: `MaxEncodedLen`)
	fn close_child_bounty_added() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1122`
		//  Estimated: `6196`
		// Minimum execution time: 80_057_000 picoseconds.
		Weight::from_parts(81_639_000, 6196)
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:3 w:3)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildrenCuratorFees` (r:1 w:1)
	/// Proof: `ChildBounties::ChildrenCuratorFees` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ParentChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBountyDescriptionsV1` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBountyDescriptionsV1` (`max_values`: None, `max_size`: Some(326), added: 2801, mode: `MaxEncodedLen`)
	fn close_child_bounty_active() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1343`
		//  Estimated: `8799`
		// Minimum execution time: 95_686_000 picoseconds.
		Weight::from_parts(99_047_000, 8799)
			.saturating_add(T::DbWeight::get().reads(7_u64))
			.saturating_add(T::DbWeight::get().writes(7_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `ChildBounties::ParentChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ParentTotalChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentTotalChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBountyDescriptionsV1` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBountyDescriptionsV1` (`max_values`: None, `max_size`: Some(326), added: 2801, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// The range of component `d` is `[0, 300]`.
	fn add_child_bounty(d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `812`
		//  Estimated: `6196`
		// Minimum execution time: 71_931_000 picoseconds.
		Weight::from_parts(75_087_378, 6196)
			// Standard Error: 526
			.saturating_add(Weight::from_parts(668, 0).saturating_mul(d.into()))
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildrenCuratorFees` (r:1 w:1)
	/// Proof: `ChildBounties::ChildrenCuratorFees` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	fn propose_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `842`
		//  Estimated: `3642`
		// Minimum execution time: 25_376_000 picoseconds.
		Weight::from_parts(26_152_000, 3642)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn accept_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1048`
		//  Estimated: `3642`
		// Minimum execution time: 40_867_000 picoseconds.
		Weight::from_parts(41_955_000, 3642)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn unassign_curator() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1048`
		//  Estimated: `3642`
		// Minimum execution time: 50_205_000 picoseconds.
		Weight::from_parts(52_117_000, 3642)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	fn award_child_bounty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `908`
		//  Estimated: `3642`
		// Minimum execution time: 27_062_000 picoseconds.
		Weight::from_parts(27_648_000, 3642)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:3 w:3)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ParentChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBountyDescriptionsV1` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBountyDescriptionsV1` (`max_values`: None, `max_size`: Some(326), added: 2801, mode: `MaxEncodedLen`)
	fn claim_child_bounty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `752`
		//  Estimated: `8799`
		// Minimum execution time: 111_020_000 picoseconds.
		Weight::from_parts(114_221_000, 8799)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildrenCuratorFees` (r:1 w:1)
	/// Proof: `ChildBounties::ChildrenCuratorFees` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ParentChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBountyDescriptionsV1` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBountyDescriptionsV1` (`max_values`: None, `max_size`: Some(326), added: 2801, mode: `MaxEncodedLen`)
	fn close_child_bounty_added() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1122`
		//  Estimated: `6196`
		// Minimum execution time: 80_057_000 picoseconds.
		Weight::from_parts(81_639_000, 6196)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: `Bounties::Bounties` (r:1 w:0)
	/// Proof: `Bounties::Bounties` (`max_values`: None, `max_size`: Some(177), added: 2652, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ChildBounties` (`max_values`: None, `max_size`: Some(145), added: 2620, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:3 w:3)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildrenCuratorFees` (r:1 w:1)
	/// Proof: `ChildBounties::ChildrenCuratorFees` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ParentChildBounties` (r:1 w:1)
	/// Proof: `ChildBounties::ParentChildBounties` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `ChildBounties::ChildBountyDescriptionsV1` (r:0 w:1)
	/// Proof: `ChildBounties::ChildBountyDescriptionsV1` (`max_values`: None, `max_size`: Some(326), added: 2801, mode: `MaxEncodedLen`)
	fn close_child_bounty_active() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1343`
		//  Estimated: `8799`
		// Minimum execution time: 95_686_000 picoseconds.
		Weight::from_parts(99_047_000, 8799)
			.saturating_add(RocksDbWeight::get().reads(7_u64))
			.saturating_add(RocksDbWeight::get().writes(7_u64))
	}
}
