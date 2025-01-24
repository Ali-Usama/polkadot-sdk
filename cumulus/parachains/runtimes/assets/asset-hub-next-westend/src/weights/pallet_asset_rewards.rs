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

//! Autogenerated weights for `pallet_asset_rewards`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-14, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-ys-ssygq-project-674-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("asset-hub-next-westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --steps=50
// --repeat=20
// --extrinsic=*
// --wasm-execution=compiled
// --heap-pages=4096
// --json-file=/builds/parity/mirrors/polkadot-sdk/.git/.artifacts/bench.json
// --pallet=pallet_asset_rewards
// --chain=asset-hub-next-westend-dev
// --header=./cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/assets/asset-hub-next-westend/src/weights/

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
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(157), added: 2632, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::PoolCost` (r:0 w:1)
	/// Proof: `AssetRewards::PoolCost` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	/// Storage: `AssetRewards::Pools` (r:0 w:1)
	/// Proof: `AssetRewards::Pools` (`max_values`: None, `max_size`: Some(1344), added: 3819, mode: `MaxEncodedLen`)
	fn create_pool() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `392`
		//  Estimated: `6360`
		// Minimum execution time: 60_734_000 picoseconds.
		Weight::from_parts(61_828_000, 0)
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
		//  Measured:  `906`
		//  Estimated: `4809`
		// Minimum execution time: 56_014_000 picoseconds.
		Weight::from_parts(58_487_000, 0)
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
		//  Measured:  `906`
		//  Estimated: `4809`
		// Minimum execution time: 59_071_000 picoseconds.
		Weight::from_parts(60_631_000, 0)
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
		//  Measured:  `1106`
		//  Estimated: `6208`
		// Minimum execution time: 80_585_000 picoseconds.
		Weight::from_parts(82_186_000, 0)
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
		// Minimum execution time: 17_083_000 picoseconds.
		Weight::from_parts(17_816_000, 0)
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
		// Minimum execution time: 15_269_000 picoseconds.
		Weight::from_parts(15_881_000, 0)
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
		// Minimum execution time: 17_482_000 picoseconds.
		Weight::from_parts(18_124_000, 0)
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
		//  Measured:  `781`
		//  Estimated: `6208`
		// Minimum execution time: 66_644_000 picoseconds.
		Weight::from_parts(67_950_000, 0)
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
	/// Storage: `AssetRewards::PoolCost` (r:1 w:1)
	/// Proof: `AssetRewards::PoolCost` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(157), added: 2632, mode: `MaxEncodedLen`)
	/// Storage: `AssetsFreezer::Freezes` (r:0 w:1)
	/// Proof: `AssetsFreezer::Freezes` (`max_values`: None, `max_size`: Some(87), added: 2562, mode: `MaxEncodedLen`)
	fn cleanup_pool() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1139`
		//  Estimated: `6208`
		// Minimum execution time: 124_136_000 picoseconds.
		Weight::from_parts(128_642_000, 0)
			.saturating_add(Weight::from_parts(0, 6208))
			.saturating_add(T::DbWeight::get().reads(10))
			.saturating_add(T::DbWeight::get().writes(10))
	}
}
