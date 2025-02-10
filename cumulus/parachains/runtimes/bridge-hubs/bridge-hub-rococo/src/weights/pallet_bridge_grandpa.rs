// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Cumulus.
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

//! Autogenerated weights for `pallet_bridge_grandpa`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2024-08-15, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-696hpswk-project-674-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("bridge-hub-rococo-dev")`, DB CACHE: 1024

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
// --pallet=pallet_bridge_grandpa
// --chain=bridge-hub-rococo-dev
// --header=./cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/bridge-hubs/bridge-hub-rococo/src/weights/

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::Weight};
use core::marker::PhantomData;

/// Weight functions for `pallet_bridge_grandpa`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_bridge_grandpa::WeightInfo for WeightInfo<T> {
	/// Storage: `BridgeWestendGrandpa::CurrentAuthoritySet` (r:1 w:0)
	/// Proof: `BridgeWestendGrandpa::CurrentAuthoritySet` (`max_values`: Some(1), `max_size`: Some(50250), added: 50745, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendGrandpa::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::BestFinalized` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::BestFinalized` (`max_values`: Some(1), `max_size`: Some(36), added: 531, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::FreeHeadersRemaining` (r:1 w:0)
	/// Proof: `BridgeWestendGrandpa::FreeHeadersRemaining` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHashesPointer` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::ImportedHashesPointer` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHashes` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::ImportedHashes` (`max_values`: Some(1024), `max_size`: Some(36), added: 1521, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHeaders` (r:0 w:2)
	/// Proof: `BridgeWestendGrandpa::ImportedHeaders` (`max_values`: Some(1024), `max_size`: Some(68), added: 1553, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[1, 168]`.
	/// The range of component `v` is `[50, 100]`.
	fn submit_finality_proof(p: u32, v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `438 + p * (60 ±0)`
		//  Estimated: `51735`
		// Minimum execution time: 313_304_000 picoseconds.
		Weight::from_parts(20_632_995, 0)
			.saturating_add(Weight::from_parts(0, 51735))
			// Standard Error: 13_694
			.saturating_add(Weight::from_parts(40_797_990, 0).saturating_mul(p.into()))
			// Standard Error: 45_696
			.saturating_add(Weight::from_parts(2_594_504, 0).saturating_mul(v.into()))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `BridgeWestendGrandpa::CurrentAuthoritySet` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::CurrentAuthoritySet` (`max_values`: Some(1), `max_size`: Some(50250), added: 50745, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHashesPointer` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::ImportedHashesPointer` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHashes` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::ImportedHashes` (`max_values`: Some(1024), `max_size`: Some(36), added: 1521, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::BestFinalized` (r:0 w:1)
	/// Proof: `BridgeWestendGrandpa::BestFinalized` (`max_values`: Some(1), `max_size`: Some(36), added: 531, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHeaders` (r:0 w:2)
	/// Proof: `BridgeWestendGrandpa::ImportedHeaders` (`max_values`: Some(1024), `max_size`: Some(68), added: 1553, mode: `MaxEncodedLen`)
	fn force_set_pallet_state() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `452`
		//  Estimated: `51735`
		// Minimum execution time: 98_033_000 picoseconds.
		Weight::from_parts(117_394_000, 0)
			.saturating_add(Weight::from_parts(0, 51735))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(6))
	}
}
