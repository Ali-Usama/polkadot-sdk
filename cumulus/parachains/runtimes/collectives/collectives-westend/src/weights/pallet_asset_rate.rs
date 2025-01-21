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

//! Autogenerated weights for `pallet_asset_rate`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `2ef552afe55a`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("collectives-westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=collectives-westend-dev
// --pallet=pallet_asset_rate
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/collectives/collectives-westend/src/weights
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

/// Weight functions for `pallet_asset_rate`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_asset_rate::WeightInfo for WeightInfo<T> {
	/// Storage: `AssetRate::ConversionRateToNative` (r:1 w:1)
	/// Proof: `AssetRate::ConversionRateToNative` (`max_values`: None, `max_size`: Some(1238), added: 3713, mode: `MaxEncodedLen`)
	fn create() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6`
		//  Estimated: `4703`
		// Minimum execution time: 12_074_000 picoseconds.
		Weight::from_parts(12_572_000, 0)
			.saturating_add(Weight::from_parts(0, 4703))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `AssetRate::ConversionRateToNative` (r:1 w:1)
	/// Proof: `AssetRate::ConversionRateToNative` (`max_values`: None, `max_size`: Some(1238), added: 3713, mode: `MaxEncodedLen`)
	fn update() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `73`
		//  Estimated: `4703`
		// Minimum execution time: 12_659_000 picoseconds.
		Weight::from_parts(13_035_000, 0)
			.saturating_add(Weight::from_parts(0, 4703))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `AssetRate::ConversionRateToNative` (r:1 w:1)
	/// Proof: `AssetRate::ConversionRateToNative` (`max_values`: None, `max_size`: Some(1238), added: 3713, mode: `MaxEncodedLen`)
	fn remove() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `73`
		//  Estimated: `4703`
		// Minimum execution time: 13_634_000 picoseconds.
		Weight::from_parts(14_030_000, 0)
			.saturating_add(Weight::from_parts(0, 4703))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
