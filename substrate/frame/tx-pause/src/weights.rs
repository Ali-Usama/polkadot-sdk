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

//! Autogenerated weights for `pallet_tx_pause`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `802a4f773b26`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: `1024`

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/kitchensink-runtime/kitchensink_runtime.wasm
// --pallet=pallet_tx_pause
// --header=/__w/polkadot-sdk/polkadot-sdk/substrate/HEADER-APACHE2
// --output=/__w/polkadot-sdk/polkadot-sdk/substrate/frame/tx-pause/src/weights.rs
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

/// Weight functions needed for `pallet_tx_pause`.
pub trait WeightInfo {
	fn pause() -> Weight;
	fn unpause() -> Weight;
}

/// Weights for `pallet_tx_pause` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `TxPause::PausedCalls` (r:1 w:1)
	/// Proof: `TxPause::PausedCalls` (`max_values`: None, `max_size`: Some(532), added: 3007, mode: `MaxEncodedLen`)
	fn pause() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `3997`
		// Minimum execution time: 9_628_000 picoseconds.
		Weight::from_parts(9_957_000, 3997)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `TxPause::PausedCalls` (r:1 w:1)
	/// Proof: `TxPause::PausedCalls` (`max_values`: None, `max_size`: Some(532), added: 3007, mode: `MaxEncodedLen`)
	fn unpause() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `3997`
		// Minimum execution time: 12_298_000 picoseconds.
		Weight::from_parts(12_507_000, 3997)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `TxPause::PausedCalls` (r:1 w:1)
	/// Proof: `TxPause::PausedCalls` (`max_values`: None, `max_size`: Some(532), added: 3007, mode: `MaxEncodedLen`)
	fn pause() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `3997`
		// Minimum execution time: 9_628_000 picoseconds.
		Weight::from_parts(9_957_000, 3997)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `TxPause::PausedCalls` (r:1 w:1)
	/// Proof: `TxPause::PausedCalls` (`max_values`: None, `max_size`: Some(532), added: 3007, mode: `MaxEncodedLen`)
	fn unpause() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `3997`
		// Minimum execution time: 12_298_000 picoseconds.
		Weight::from_parts(12_507_000, 3997)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
}
