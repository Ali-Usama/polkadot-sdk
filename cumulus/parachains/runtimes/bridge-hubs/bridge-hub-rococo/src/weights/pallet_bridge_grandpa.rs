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

//! Autogenerated weights for `pallet_bridge_grandpa`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-30, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `569cf895a746`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/bridge-hub-rococo-runtime/bridge_hub_rococo_runtime.wasm
// --pallet=pallet_bridge_grandpa
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/bridge-hubs/bridge-hub-rococo/src/weights
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

/// Weight functions for `pallet_bridge_grandpa`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_bridge_grandpa::WeightInfo for WeightInfo<T> {
	/// Storage: `BridgeWestendGrandpa::CurrentAuthoritySet` (r:1 w:0)
	/// Proof: `BridgeWestendGrandpa::CurrentAuthoritySet` (`max_values`: Some(1), `max_size`: Some(50250), added: 50745, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendGrandpa::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::BestFinalized` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::BestFinalized` (`max_values`: Some(1), `max_size`: Some(36), added: 531, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHashesPointer` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::ImportedHashesPointer` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHashes` (r:1 w:1)
	/// Proof: `BridgeWestendGrandpa::ImportedHashes` (`max_values`: Some(1024), `max_size`: Some(36), added: 1521, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendGrandpa::ImportedHeaders` (r:0 w:2)
	/// Proof: `BridgeWestendGrandpa::ImportedHeaders` (`max_values`: Some(1024), `max_size`: Some(68), added: 1553, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[1, 168]`.
	/// The range of component `v` is `[50, 100]`.
	fn submit_finality_proof(p: u32, _v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `31 + p * (60 ±0)`
		//  Estimated: `51735`
		// Minimum execution time: 320_957_000 picoseconds.
		Weight::from_parts(332_720_000, 0)
			.saturating_add(Weight::from_parts(0, 51735))
			// Standard Error: 42_713
			.saturating_add(Weight::from_parts(43_493_374, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(5))
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
		//  Measured:  `84`
		//  Estimated: `51735`
		// Minimum execution time: 103_320_000 picoseconds.
		Weight::from_parts(122_625_000, 0)
			.saturating_add(Weight::from_parts(0, 51735))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(6))
	}
}
