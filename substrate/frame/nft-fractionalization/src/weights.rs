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

//! Autogenerated weights for `pallet_nft_fractionalization`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `4563561839a5`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: `1024`

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/kitchensink-runtime/kitchensink_runtime.wasm
// --pallet=pallet_nft_fractionalization
// --header=/__w/polkadot-sdk/polkadot-sdk/substrate/HEADER-APACHE2
// --output=/__w/polkadot-sdk/polkadot-sdk/substrate/frame/nft-fractionalization/src/weights.rs
// --wasm-execution=compiled
// --steps=50
// --repeat=20
// --heap-pages=4096
// --template=substrate/.maintain/frame-weight-template.hbs
// --no-storage-info
// --no-min-squares
// --no-median-slopes
// --genesis-builder-policy=none
// --exclude-pallets=pallet_xcm,pallet_xcm_benchmarks::fungible,pallet_xcm_benchmarks::generic,pallet_nomination_pools,pallet_remark,pallet_transaction_storage,pallet_election_provider_multi_block,pallet_election_provider_multi_block::signed,pallet_election_provider_multi_block::unsigned,pallet_election_provider_multi_block::verifier

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]
#![allow(dead_code)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for `pallet_nft_fractionalization`.
pub trait WeightInfo {
	fn fractionalize() -> Weight;
	fn unify() -> Weight;
}

/// Weights for `pallet_nft_fractionalization` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `Nfts::Item` (r:1 w:0)
	/// Proof: `Nfts::Item` (`max_values`: None, `max_size`: Some(861), added: 3336, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Attribute` (r:1 w:1)
	/// Proof: `Nfts::Attribute` (`max_values`: None, `max_size`: Some(479), added: 2954, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Collection` (r:1 w:1)
	/// Proof: `Nfts::Collection` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Asset` (r:1 w:1)
	/// Proof: `Assets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `Assets::NextAssetId` (r:1 w:0)
	/// Proof: `Assets::NextAssetId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:1 w:1)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Metadata` (r:1 w:1)
	/// Proof: `Assets::Metadata` (`max_values`: None, `max_size`: Some(140), added: 2615, mode: `MaxEncodedLen`)
	/// Storage: `NftFractionalization::NftToAsset` (r:0 w:1)
	/// Proof: `NftFractionalization::NftToAsset` (`max_values`: None, `max_size`: Some(92), added: 2567, mode: `MaxEncodedLen`)
	fn fractionalize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `364`
		//  Estimated: `4326`
		// Minimum execution time: 173_042_000 picoseconds.
		Weight::from_parts(176_398_000, 4326)
			.saturating_add(T::DbWeight::get().reads(9_u64))
			.saturating_add(T::DbWeight::get().writes(8_u64))
	}
	/// Storage: `NftFractionalization::NftToAsset` (r:1 w:1)
	/// Proof: `NftFractionalization::NftToAsset` (`max_values`: None, `max_size`: Some(92), added: 2567, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Asset` (r:1 w:1)
	/// Proof: `Assets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:1 w:1)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Attribute` (r:1 w:1)
	/// Proof: `Nfts::Attribute` (`max_values`: None, `max_size`: Some(479), added: 2954, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Collection` (r:1 w:1)
	/// Proof: `Nfts::Collection` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::CollectionConfigOf` (r:1 w:0)
	/// Proof: `Nfts::CollectionConfigOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::ItemConfigOf` (r:1 w:0)
	/// Proof: `Nfts::ItemConfigOf` (`max_values`: None, `max_size`: Some(48), added: 2523, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Item` (r:1 w:1)
	/// Proof: `Nfts::Item` (`max_values`: None, `max_size`: Some(861), added: 3336, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Account` (r:0 w:1)
	/// Proof: `Nfts::Account` (`max_values`: None, `max_size`: Some(88), added: 2563, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::ItemPriceOf` (r:0 w:1)
	/// Proof: `Nfts::ItemPriceOf` (`max_values`: None, `max_size`: Some(89), added: 2564, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::PendingSwapOf` (r:0 w:1)
	/// Proof: `Nfts::PendingSwapOf` (`max_values`: None, `max_size`: Some(71), added: 2546, mode: `MaxEncodedLen`)
	fn unify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1174`
		//  Estimated: `4326`
		// Minimum execution time: 124_038_000 picoseconds.
		Weight::from_parts(127_219_000, 4326)
			.saturating_add(T::DbWeight::get().reads(9_u64))
			.saturating_add(T::DbWeight::get().writes(10_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `Nfts::Item` (r:1 w:0)
	/// Proof: `Nfts::Item` (`max_values`: None, `max_size`: Some(861), added: 3336, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Attribute` (r:1 w:1)
	/// Proof: `Nfts::Attribute` (`max_values`: None, `max_size`: Some(479), added: 2954, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Collection` (r:1 w:1)
	/// Proof: `Nfts::Collection` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Asset` (r:1 w:1)
	/// Proof: `Assets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `Assets::NextAssetId` (r:1 w:0)
	/// Proof: `Assets::NextAssetId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:1 w:1)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Metadata` (r:1 w:1)
	/// Proof: `Assets::Metadata` (`max_values`: None, `max_size`: Some(140), added: 2615, mode: `MaxEncodedLen`)
	/// Storage: `NftFractionalization::NftToAsset` (r:0 w:1)
	/// Proof: `NftFractionalization::NftToAsset` (`max_values`: None, `max_size`: Some(92), added: 2567, mode: `MaxEncodedLen`)
	fn fractionalize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `364`
		//  Estimated: `4326`
		// Minimum execution time: 173_042_000 picoseconds.
		Weight::from_parts(176_398_000, 4326)
			.saturating_add(RocksDbWeight::get().reads(9_u64))
			.saturating_add(RocksDbWeight::get().writes(8_u64))
	}
	/// Storage: `NftFractionalization::NftToAsset` (r:1 w:1)
	/// Proof: `NftFractionalization::NftToAsset` (`max_values`: None, `max_size`: Some(92), added: 2567, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Asset` (r:1 w:1)
	/// Proof: `Assets::Asset` (`max_values`: None, `max_size`: Some(210), added: 2685, mode: `MaxEncodedLen`)
	/// Storage: `Assets::Account` (r:1 w:1)
	/// Proof: `Assets::Account` (`max_values`: None, `max_size`: Some(134), added: 2609, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Attribute` (r:1 w:1)
	/// Proof: `Nfts::Attribute` (`max_values`: None, `max_size`: Some(479), added: 2954, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Collection` (r:1 w:1)
	/// Proof: `Nfts::Collection` (`max_values`: None, `max_size`: Some(84), added: 2559, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::CollectionConfigOf` (r:1 w:0)
	/// Proof: `Nfts::CollectionConfigOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::ItemConfigOf` (r:1 w:0)
	/// Proof: `Nfts::ItemConfigOf` (`max_values`: None, `max_size`: Some(48), added: 2523, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Item` (r:1 w:1)
	/// Proof: `Nfts::Item` (`max_values`: None, `max_size`: Some(861), added: 3336, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(427), added: 2902, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::Account` (r:0 w:1)
	/// Proof: `Nfts::Account` (`max_values`: None, `max_size`: Some(88), added: 2563, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::ItemPriceOf` (r:0 w:1)
	/// Proof: `Nfts::ItemPriceOf` (`max_values`: None, `max_size`: Some(89), added: 2564, mode: `MaxEncodedLen`)
	/// Storage: `Nfts::PendingSwapOf` (r:0 w:1)
	/// Proof: `Nfts::PendingSwapOf` (`max_values`: None, `max_size`: Some(71), added: 2546, mode: `MaxEncodedLen`)
	fn unify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1174`
		//  Estimated: `4326`
		// Minimum execution time: 124_038_000 picoseconds.
		Weight::from_parts(127_219_000, 4326)
			.saturating_add(RocksDbWeight::get().reads(9_u64))
			.saturating_add(RocksDbWeight::get().writes(10_u64))
	}
}
