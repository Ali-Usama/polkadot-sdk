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

//! Autogenerated weights for `pallet_asset_conversion`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-11, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `a7901b5928f1`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/asset-hub-rococo-runtime/asset_hub_rococo_runtime.wasm
// --pallet=pallet_asset_conversion
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

/// Weight functions for `pallet_asset_conversion`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_asset_conversion::WeightInfo for WeightInfo<T> {
	/// Storage: `AssetConversion::Pools` (r:1 w:1)
	/// Proof: `AssetConversion::Pools` (`max_values`: None, `max_size`: Some(1224), added: 3699, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Asset` (r:1 w:0)
	/// Proof: `ForeignAssets::Asset` (`max_values`: None, `max_size`: Some(808), added: 3283, mode: `MaxEncodedLen`)
	/// Storage: `AssetConversion::NextPoolAssetId` (r:1 w:1)
	/// Proof: `AssetConversion::NextPoolAssetId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::Asset` (r:1 w:1)
	/// Proof: `PoolAssets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::NextAssetId` (r:1 w:0)
	/// Proof: `PoolAssets::NextAssetId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::Account` (r:1 w:1)
	/// Proof: `PoolAssets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	fn create_pool() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `365`
		//  Estimated: `4689`
		// Minimum execution time: 64_159_000 picoseconds.
		Weight::from_parts(66_300_000, 0)
			.saturating_add(Weight::from_parts(0, 4689))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `AssetConversion::Pools` (r:1 w:0)
	/// Proof: `AssetConversion::Pools` (`max_values`: None, `max_size`: Some(1224), added: 3699, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Asset` (r:1 w:1)
	/// Proof: `ForeignAssets::Asset` (`max_values`: None, `max_size`: Some(808), added: 3283, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Account` (r:2 w:2)
	/// Proof: `ForeignAssets::Account` (`max_values`: None, `max_size`: Some(732), added: 3207, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssetsFreezer::FrozenBalances` (r:1 w:0)
	/// Proof: `ForeignAssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(682), added: 3157, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::Asset` (r:1 w:1)
	/// Proof: `PoolAssets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::Account` (r:2 w:2)
	/// Proof: `PoolAssets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	fn add_liquidity() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `929`
		//  Estimated: `7404`
		// Minimum execution time: 158_903_000 picoseconds.
		Weight::from_parts(162_969_000, 0)
			.saturating_add(Weight::from_parts(0, 7404))
			.saturating_add(T::DbWeight::get().reads(9))
			.saturating_add(T::DbWeight::get().writes(7))
	}
	/// Storage: `AssetConversion::Pools` (r:1 w:0)
	/// Proof: `AssetConversion::Pools` (`max_values`: None, `max_size`: Some(1224), added: 3699, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Asset` (r:1 w:1)
	/// Proof: `ForeignAssets::Asset` (`max_values`: None, `max_size`: Some(808), added: 3283, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Account` (r:2 w:2)
	/// Proof: `ForeignAssets::Account` (`max_values`: None, `max_size`: Some(732), added: 3207, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssetsFreezer::FrozenBalances` (r:1 w:0)
	/// Proof: `ForeignAssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(682), added: 3157, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::Asset` (r:1 w:1)
	/// Proof: `PoolAssets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::Account` (r:1 w:1)
	/// Proof: `PoolAssets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssetsFreezer::FrozenBalances` (r:1 w:0)
	/// Proof: `PoolAssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	fn remove_liquidity() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1141`
		//  Estimated: `7404`
		// Minimum execution time: 162_959_000 picoseconds.
		Weight::from_parts(167_704_000, 0)
			.saturating_add(Weight::from_parts(0, 7404))
			.saturating_add(T::DbWeight::get().reads(9))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `ForeignAssets::Asset` (r:2 w:2)
	/// Proof: `ForeignAssets::Asset` (`max_values`: None, `max_size`: Some(808), added: 3283, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Account` (r:4 w:4)
	/// Proof: `ForeignAssets::Account` (`max_values`: None, `max_size`: Some(732), added: 3207, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssetsFreezer::FrozenBalances` (r:3 w:0)
	/// Proof: `ForeignAssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(682), added: 3157, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[2, 3]`.
	fn swap_exact_tokens_for_tokens(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0 + n * (507 ±0)`
		//  Estimated: `7404 + n * (3157 ±19)`
		// Minimum execution time: 106_211_000 picoseconds.
		Weight::from_parts(109_155_000, 0)
			.saturating_add(Weight::from_parts(0, 7404))
			// Standard Error: 209_014
			.saturating_add(Weight::from_parts(1_679_111, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(4))
			.saturating_add(Weight::from_parts(0, 3157).saturating_mul(n.into()))
	}
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Asset` (r:2 w:2)
	/// Proof: `ForeignAssets::Asset` (`max_values`: None, `max_size`: Some(808), added: 3283, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Account` (r:4 w:4)
	/// Proof: `ForeignAssets::Account` (`max_values`: None, `max_size`: Some(732), added: 3207, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssetsFreezer::FrozenBalances` (r:3 w:0)
	/// Proof: `ForeignAssetsFreezer::FrozenBalances` (`max_values`: None, `max_size`: Some(682), added: 3157, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[2, 3]`.
	fn swap_tokens_for_exact_tokens(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0 + n * (507 ±0)`
		//  Estimated: `7404 + n * (3157 ±10)`
		// Minimum execution time: 106_348_000 picoseconds.
		Weight::from_parts(109_262_000, 0)
			.saturating_add(Weight::from_parts(0, 7404))
			// Standard Error: 211_081
			.saturating_add(Weight::from_parts(1_680_474, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(4))
			.saturating_add(Weight::from_parts(0, 3157).saturating_mul(n.into()))
	}
	/// Storage: `AssetConversion::Pools` (r:1 w:0)
	/// Proof: `AssetConversion::Pools` (`max_values`: None, `max_size`: Some(1224), added: 3699, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Asset` (r:1 w:1)
	/// Proof: `ForeignAssets::Asset` (`max_values`: None, `max_size`: Some(808), added: 3283, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ForeignAssets::Account` (r:1 w:1)
	/// Proof: `ForeignAssets::Account` (`max_values`: None, `max_size`: Some(732), added: 3207, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::Asset` (r:1 w:1)
	/// Proof: `PoolAssets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `PoolAssets::Account` (r:1 w:1)
	/// Proof: `PoolAssets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 3]`.
	fn touch(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `938`
		//  Estimated: `4689`
		// Minimum execution time: 44_426_000 picoseconds.
		Weight::from_parts(50_396_140, 0)
			.saturating_add(Weight::from_parts(0, 4689))
			// Standard Error: 286_180
			.saturating_add(Weight::from_parts(11_484_433, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(n.into())))
	}
}
