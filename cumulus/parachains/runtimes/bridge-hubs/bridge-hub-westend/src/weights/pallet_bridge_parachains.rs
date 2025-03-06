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

//! Autogenerated weights for `pallet_bridge_parachains`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `d3b41be4aae8`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/bridge-hub-westend-runtime/bridge_hub_westend_runtime.wasm
// --pallet=pallet_bridge_parachains
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/bridge-hubs/bridge-hub-westend/src/weights
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

/// Weight functions for `pallet_bridge_parachains`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_bridge_parachains::WeightInfo for WeightInfo<T> {
	/// Storage: `BridgeRococoParachains::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeRococoParachains::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoGrandpa::ImportedHeaders` (r:1 w:0)
	/// Proof: `BridgeRococoGrandpa::ImportedHeaders` (`max_values`: Some(1024), `max_size`: Some(68), added: 1553, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ParasInfo` (r:1 w:1)
	/// Proof: `BridgeRococoParachains::ParasInfo` (`max_values`: Some(1), `max_size`: Some(60), added: 555, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ImportedParaHashes` (r:1 w:1)
	/// Proof: `BridgeRococoParachains::ImportedParaHashes` (`max_values`: Some(64), `max_size`: Some(64), added: 1054, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ImportedParaHeads` (r:0 w:1)
	/// Proof: `BridgeRococoParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[1, 2]`.
	fn submit_parachain_heads_with_n_parachains(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `83`
		//  Estimated: `2543`
		// Minimum execution time: 35_560_000 picoseconds.
		Weight::from_parts(37_182_961, 0)
			.saturating_add(Weight::from_parts(0, 2543))
			// Standard Error: 100_736
			.saturating_add(Weight::from_parts(42_669, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `BridgeRococoParachains::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeRococoParachains::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoGrandpa::ImportedHeaders` (r:1 w:0)
	/// Proof: `BridgeRococoGrandpa::ImportedHeaders` (`max_values`: Some(1024), `max_size`: Some(68), added: 1553, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ParasInfo` (r:1 w:1)
	/// Proof: `BridgeRococoParachains::ParasInfo` (`max_values`: Some(1), `max_size`: Some(60), added: 555, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ImportedParaHashes` (r:1 w:1)
	/// Proof: `BridgeRococoParachains::ImportedParaHashes` (`max_values`: Some(64), `max_size`: Some(64), added: 1054, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ImportedParaHeads` (r:0 w:1)
	/// Proof: `BridgeRococoParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	fn submit_parachain_heads_with_1kb_proof() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `83`
		//  Estimated: `2543`
		// Minimum execution time: 37_572_000 picoseconds.
		Weight::from_parts(38_392_000, 0)
			.saturating_add(Weight::from_parts(0, 2543))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `BridgeRococoParachains::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeRococoParachains::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoGrandpa::ImportedHeaders` (r:1 w:0)
	/// Proof: `BridgeRococoGrandpa::ImportedHeaders` (`max_values`: Some(1024), `max_size`: Some(68), added: 1553, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ParasInfo` (r:1 w:1)
	/// Proof: `BridgeRococoParachains::ParasInfo` (`max_values`: Some(1), `max_size`: Some(60), added: 555, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ImportedParaHashes` (r:1 w:1)
	/// Proof: `BridgeRococoParachains::ImportedParaHashes` (`max_values`: Some(64), `max_size`: Some(64), added: 1054, mode: `MaxEncodedLen`)
	/// Storage: `BridgeRococoParachains::ImportedParaHeads` (r:0 w:1)
	/// Proof: `BridgeRococoParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	fn submit_parachain_heads_with_16kb_proof() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `83`
		//  Estimated: `2543`
		// Minimum execution time: 66_029_000 picoseconds.
		Weight::from_parts(67_174_000, 0)
			.saturating_add(Weight::from_parts(0, 2543))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
}
