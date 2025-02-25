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

//! Autogenerated weights for `pallet_asset_rewards`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `ebe189bd6afc`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/asset-hub-rococo-runtime/asset_hub_rococo_runtime.wasm
// --pallet=pallet_asset_rewards
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/assets/asset-hub-rococo/src/weights
// --wasm-execution=compiled
// --steps=50
// --repeat=20
// --heap-pages=4096
// --no-storage-info
// --no-min-squares
// --no-median-slopes

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::Weight};
use core::marker::PhantomData;

/// Weight functions for `pallet_asset_rewards`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_asset_rewards::WeightInfo for WeightInfo<T> {
	/// Storage: `Assets::Asset` (r:2 w:0)
	/// Proof: `Assets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::NextPoolId` (r:1 w:1)
	/// Proof: `AssetRewards::NextPoolId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(85), added: 2560, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::PoolCost` (r:0 w:1)
	/// Proof: `AssetRewards::PoolCost` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::Pools` (r:0 w:1)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	fn create_pool() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `358`
		//  Estimated: `6360`
		// Minimum execution time: 63_287_000 picoseconds.
		Weight::from_parts(65_064_000, 0)
			.saturating_add(Weight::from_parts(0, 6360))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `AssetRewards::Pools` (r:1 w:1)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::PoolStakers` (r:1 w:1)
	/// Proof: `AssetRewards::PoolStakers` (`max_values`: None, `max_size`: Some(116), added: 2591, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::Freezes` (r:1 w:1)
	/// Proof: `AssetsFreezer::Freezes` (`max_values`: None, `max_size`: Some(87), added: 2562, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:1 w:0)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::FrozenBalances` (r:1 w:1)
	/// Proof: `AssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	fn stake() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `872`
		//  Estimated: `4809`
		// Minimum execution time: 54_566_000 picoseconds.
		Weight::from_parts(55_939_000, 0)
			.saturating_add(Weight::from_parts(0, 4809))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `AssetRewards::Pools` (r:1 w:1)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::PoolStakers` (r:1 w:1)
	/// Proof: `AssetRewards::PoolStakers` (`max_values`: None, `max_size`: Some(116), added: 2591, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::Freezes` (r:1 w:1)
	/// Proof: `AssetsFreezer::Freezes` (`max_values`: None, `max_size`: Some(87), added: 2562, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:1 w:0)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::FrozenBalances` (r:1 w:1)
	/// Proof: `AssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	fn unstake() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `872`
		//  Estimated: `4809`
		// Minimum execution time: 58_037_000 picoseconds.
		Weight::from_parts(60_125_000, 0)
			.saturating_add(Weight::from_parts(0, 4809))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `AssetRewards::Pools` (r:1 w:0)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::PoolStakers` (r:1 w:1)
	/// Proof: `AssetRewards::PoolStakers` (`max_values`: None, `max_size`: Some(116), added: 2591, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Asset` (r:1 w:1)
	/// Proof: `Assets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:2 w:2)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::FrozenBalances` (r:1 w:0)
	/// Proof: `AssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	fn harvest_rewards() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1072`
		//  Estimated: `6208`
		// Minimum execution time: 78_990_000 picoseconds.
		Weight::from_parts(81_455_000, 0)
			.saturating_add(Weight::from_parts(0, 6208))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `AssetRewards::Pools` (r:1 w:1)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	fn set_pool_reward_rate_per_block() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `318`
		//  Estimated: `4809`
		// Minimum execution time: 16_720_000 picoseconds.
		Weight::from_parts(17_616_000, 0)
			.saturating_add(Weight::from_parts(0, 4809))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `AssetRewards::Pools` (r:1 w:1)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	fn set_pool_admin() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `318`
		//  Estimated: `4809`
		// Minimum execution time: 15_342_000 picoseconds.
		Weight::from_parts(16_001_000, 0)
			.saturating_add(Weight::from_parts(0, 4809))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `AssetRewards::Pools` (r:1 w:1)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	fn set_pool_expiry_block() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `318`
		//  Estimated: `4809`
		// Minimum execution time: 18_190_000 picoseconds.
		Weight::from_parts(18_684_000, 0)
			.saturating_add(Weight::from_parts(0, 4809))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `AssetRewards::Pools` (r:1 w:0)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Asset` (r:1 w:1)
	/// Proof: `Assets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:2 w:2)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::FrozenBalances` (r:1 w:0)
	/// Proof: `AssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn deposit_reward_tokens() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `747`
		//  Estimated: `6208`
		// Minimum execution time: 66_061_000 picoseconds.
		Weight::from_parts(67_730_000, 0)
			.saturating_add(Weight::from_parts(0, 6208))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `AssetRewards::Pools` (r:1 w:1)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::PoolStakers` (r:1 w:0)
	/// Proof: `AssetRewards::PoolStakers` (`max_values`: None, `max_size`: Some(116), added: 2591, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Asset` (r:1 w:1)
	/// Proof: `Assets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:2 w:2)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::FrozenBalances` (r:1 w:1)
	/// Proof: `AssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::Freezes` (r:1 w:1)
	/// Proof: `AssetsFreezer::Freezes` (`max_values`: None, `max_size`: Some(87), added: 2562, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::PoolCost` (r:1 w:1)
	/// Proof: `AssetRewards::PoolCost` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(85), added: 2560, mode: `MaxEncodedLen`)
	fn cleanup_pool() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1105`
		//  Estimated: `6208`
		// Minimum execution time: 127_043_000 picoseconds.
		Weight::from_parts(130_900_000, 0)
			.saturating_add(Weight::from_parts(0, 6208))
			.saturating_add(T::DbWeight::get().reads(11))
			.saturating_add(T::DbWeight::get().writes(10))
	}
}
