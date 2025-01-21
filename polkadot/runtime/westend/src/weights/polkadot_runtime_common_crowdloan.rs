// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Autogenerated weights for `polkadot_runtime_common::crowdloan`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `281d1f3fe473`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot
// benchmark
// pallet
// --extrinsic=*
// --chain=westend-dev
// --pallet=polkadot_runtime_common::crowdloan
// --header=/__w/polkadot-sdk/polkadot-sdk/polkadot/file_header.txt
// --output=./polkadot/runtime/westend/src/weights
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

/// Weight functions for `polkadot_runtime_common::crowdloan`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> polkadot_runtime_common::crowdloan::WeightInfo for WeightInfo<T> {
	/// Storage: `Crowdloan::Funds` (r:1 w:1)
	/// Proof: `Crowdloan::Funds` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Registrar::Paras` (r:1 w:0)
	/// Proof: `Registrar::Paras` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::ParaLifecycles` (r:1 w:0)
	/// Proof: `Paras::ParaLifecycles` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Crowdloan::NextFundIndex` (r:1 w:1)
	/// Proof: `Crowdloan::NextFundIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn create() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `400`
		//  Estimated: `3865`
		// Minimum execution time: 57_343_000 picoseconds.
		Weight::from_parts(61_773_000, 0)
			.saturating_add(Weight::from_parts(0, 3865))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Crowdloan::Funds` (r:1 w:1)
	/// Proof: `Crowdloan::Funds` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Slots::Leases` (r:1 w:0)
	/// Proof: `Slots::Leases` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Auctions::AuctionInfo` (r:1 w:0)
	/// Proof: `Auctions::AuctionInfo` (`max_values`: Some(1), `max_size`: Some(8), added: 503, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Crowdloan::EndingsCount` (r:1 w:0)
	/// Proof: `Crowdloan::EndingsCount` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Crowdloan::NewRaise` (r:1 w:1)
	/// Proof: `Crowdloan::NewRaise` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: UNKNOWN KEY `0xd861ea1ebf4800d4b89f4ff787ad79ee96d9a708c85b57da7eb8f9ddeda61291` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0xd861ea1ebf4800d4b89f4ff787ad79ee96d9a708c85b57da7eb8f9ddeda61291` (r:1 w:1)
	fn contribute() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `530`
		//  Estimated: `3995`
		// Minimum execution time: 135_445_000 picoseconds.
		Weight::from_parts(140_995_000, 0)
			.saturating_add(Weight::from_parts(0, 3995))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `Crowdloan::Funds` (r:1 w:1)
	/// Proof: `Crowdloan::Funds` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0xc85982571aa615c788ef9b2c16f54f25773fd439e8ee1ed2aa3ae43d48e880f0` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0xc85982571aa615c788ef9b2c16f54f25773fd439e8ee1ed2aa3ae43d48e880f0` (r:1 w:1)
	fn withdraw() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `687`
		//  Estimated: `6196`
		// Minimum execution time: 86_362_000 picoseconds.
		Weight::from_parts(90_039_000, 0)
			.saturating_add(Weight::from_parts(0, 6196))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `k` is `[0, 500]`.
	fn refund(k: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `316 + k * (189 ±0)`
		//  Estimated: `325 + k * (190 ±0)`
		// Minimum execution time: 51_912_000 picoseconds.
		Weight::from_parts(53_070_000, 0)
			.saturating_add(Weight::from_parts(0, 325))
			// Standard Error: 14_470
			.saturating_add(Weight::from_parts(44_512_579, 0).saturating_mul(k.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().reads((2_u64).saturating_mul(k.into())))
			.saturating_add(T::DbWeight::get().writes(2))
			.saturating_add(T::DbWeight::get().writes((2_u64).saturating_mul(k.into())))
			.saturating_add(Weight::from_parts(0, 190).saturating_mul(k.into()))
	}
	/// Storage: `Crowdloan::Funds` (r:1 w:1)
	/// Proof: `Crowdloan::Funds` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn dissolve() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `514`
		//  Estimated: `6196`
		// Minimum execution time: 53_789_000 picoseconds.
		Weight::from_parts(56_914_000, 0)
			.saturating_add(Weight::from_parts(0, 6196))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Crowdloan::Funds` (r:1 w:1)
	/// Proof: `Crowdloan::Funds` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn edit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `234`
		//  Estimated: `3699`
		// Minimum execution time: 26_192_000 picoseconds.
		Weight::from_parts(28_067_000, 0)
			.saturating_add(Weight::from_parts(0, 3699))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Crowdloan::Funds` (r:1 w:0)
	/// Proof: `Crowdloan::Funds` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: UNKNOWN KEY `0xd861ea1ebf4800d4b89f4ff787ad79ee96d9a708c85b57da7eb8f9ddeda61291` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0xd861ea1ebf4800d4b89f4ff787ad79ee96d9a708c85b57da7eb8f9ddeda61291` (r:1 w:1)
	fn add_memo() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `412`
		//  Estimated: `3877`
		// Minimum execution time: 30_650_000 picoseconds.
		Weight::from_parts(31_980_000, 0)
			.saturating_add(Weight::from_parts(0, 3877))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Crowdloan::Funds` (r:1 w:0)
	/// Proof: `Crowdloan::Funds` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Crowdloan::NewRaise` (r:1 w:1)
	/// Proof: `Crowdloan::NewRaise` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn poke() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `238`
		//  Estimated: `3703`
		// Minimum execution time: 20_011_000 picoseconds.
		Weight::from_parts(20_877_000, 0)
			.saturating_add(Weight::from_parts(0, 3703))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Auctions::AuctionInfo` (r:1 w:0)
	/// Proof: `Auctions::AuctionInfo` (`max_values`: Some(1), `max_size`: Some(8), added: 503, mode: `MaxEncodedLen`)
	/// Storage: `Crowdloan::EndingsCount` (r:1 w:1)
	/// Proof: `Crowdloan::EndingsCount` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Crowdloan::NewRaise` (r:1 w:1)
	/// Proof: `Crowdloan::NewRaise` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Crowdloan::Funds` (r:100 w:0)
	/// Proof: `Crowdloan::Funds` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Auctions::AuctionCounter` (r:1 w:0)
	/// Proof: `Auctions::AuctionCounter` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Paras::ParaLifecycles` (r:100 w:0)
	/// Proof: `Paras::ParaLifecycles` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Slots::Leases` (r:100 w:0)
	/// Proof: `Slots::Leases` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Auctions::Winning` (r:1 w:1)
	/// Proof: `Auctions::Winning` (`max_values`: None, `max_size`: Some(1920), added: 4395, mode: `MaxEncodedLen`)
	/// Storage: `Auctions::ReservedAmounts` (r:100 w:100)
	/// Proof: `Auctions::ReservedAmounts` (`max_values`: None, `max_size`: Some(60), added: 2535, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:100 w:100)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[2, 100]`.
	fn on_initialize(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `233 + n * (360 ±0)`
		//  Estimated: `5385 + n * (2835 ±0)`
		// Minimum execution time: 138_415_000 picoseconds.
		Weight::from_parts(142_003_000, 0)
			.saturating_add(Weight::from_parts(0, 5385))
			// Standard Error: 69_564
			.saturating_add(Weight::from_parts(62_286_059, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().reads((5_u64).saturating_mul(n.into())))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(T::DbWeight::get().writes((2_u64).saturating_mul(n.into())))
			.saturating_add(Weight::from_parts(0, 2835).saturating_mul(n.into()))
	}
}
