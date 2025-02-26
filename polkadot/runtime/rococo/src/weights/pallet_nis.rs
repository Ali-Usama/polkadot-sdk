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

//! Autogenerated weights for `pallet_nis`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-22, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `d3a9aad6f7a3`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/rococo-runtime/rococo_runtime.wasm
// --pallet=pallet_nis
// --header=/__w/polkadot-sdk/polkadot-sdk/polkadot/file_header.txt
// --output=./polkadot/runtime/rococo/src/weights
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

/// Weight functions for `pallet_nis`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_nis::WeightInfo for WeightInfo<T> {
	/// Storage: `Parameters::Parameters` (r:1 w:0)
	/// Proof: `Parameters::Parameters` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `Nis::Queues` (r:1 w:1)
	/// Proof: `Nis::Queues` (`max_values`: None, `max_size`: Some(48022), added: 50497, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(103), added: 2578, mode: `MaxEncodedLen`)
	/// Storage: `Nis::QueueTotals` (r:1 w:1)
	/// Proof: `Nis::QueueTotals` (`max_values`: Some(1), `max_size`: Some(6002), added: 6497, mode: `MaxEncodedLen`)
	/// The range of component `l` is `[0, 999]`.
	fn place_bid(l: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6213 + l * (48 ±0)`
		//  Estimated: `51487`
		// Minimum execution time: 51_535_000 picoseconds.
		Weight::from_parts(48_054_720, 0)
			.saturating_add(Weight::from_parts(0, 51487))
			// Standard Error: 1_637
			.saturating_add(Weight::from_parts(116_321, 0).saturating_mul(l.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Parameters::Parameters` (r:1 w:0)
	/// Proof: `Parameters::Parameters` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `Nis::Queues` (r:1 w:1)
	/// Proof: `Nis::Queues` (`max_values`: None, `max_size`: Some(48022), added: 50497, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(103), added: 2578, mode: `MaxEncodedLen`)
	/// Storage: `Nis::QueueTotals` (r:1 w:1)
	/// Proof: `Nis::QueueTotals` (`max_values`: Some(1), `max_size`: Some(6002), added: 6497, mode: `MaxEncodedLen`)
	fn place_bid_max() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `54215`
		//  Estimated: `51487`
		// Minimum execution time: 173_342_000 picoseconds.
		Weight::from_parts(184_974_000, 0)
			.saturating_add(Weight::from_parts(0, 51487))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Nis::Queues` (r:1 w:1)
	/// Proof: `Nis::Queues` (`max_values`: None, `max_size`: Some(48022), added: 50497, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(103), added: 2578, mode: `MaxEncodedLen`)
	/// Storage: `Nis::QueueTotals` (r:1 w:1)
	/// Proof: `Nis::QueueTotals` (`max_values`: Some(1), `max_size`: Some(6002), added: 6497, mode: `MaxEncodedLen`)
	/// The range of component `l` is `[1, 1000]`.
	fn retract_bid(l: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6209 + l * (48 ±0)`
		//  Estimated: `51487`
		// Minimum execution time: 48_913_000 picoseconds.
		Weight::from_parts(40_310_888, 0)
			.saturating_add(Weight::from_parts(0, 51487))
			// Standard Error: 1_567
			.saturating_add(Weight::from_parts(98_720, 0).saturating_mul(l.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Nis::Summary` (r:1 w:0)
	/// Proof: `Nis::Summary` (`max_values`: Some(1), `max_size`: Some(40), added: 535, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn fund_deficit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `225`
		//  Estimated: `3593`
		// Minimum execution time: 33_430_000 picoseconds.
		Weight::from_parts(34_693_000, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Nis::Receipts` (r:1 w:1)
	/// Proof: `Nis::Receipts` (`max_values`: None, `max_size`: Some(81), added: 2556, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(103), added: 2578, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Nis::Summary` (r:1 w:1)
	/// Proof: `Nis::Summary` (`max_values`: Some(1), `max_size`: Some(40), added: 535, mode: `MaxEncodedLen`)
	/// Storage: `NisCounterpartBalances::Account` (r:1 w:1)
	/// Proof: `NisCounterpartBalances::Account` (`max_values`: None, `max_size`: Some(112), added: 2587, mode: `MaxEncodedLen`)
	fn communify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `387`
		//  Estimated: `3593`
		// Minimum execution time: 70_761_000 picoseconds.
		Weight::from_parts(72_954_000, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `Nis::Receipts` (r:1 w:1)
	/// Proof: `Nis::Receipts` (`max_values`: None, `max_size`: Some(81), added: 2556, mode: `MaxEncodedLen`)
	/// Storage: `Nis::Summary` (r:1 w:1)
	/// Proof: `Nis::Summary` (`max_values`: Some(1), `max_size`: Some(40), added: 535, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `NisCounterpartBalances::Account` (r:1 w:1)
	/// Proof: `NisCounterpartBalances::Account` (`max_values`: None, `max_size`: Some(112), added: 2587, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(103), added: 2578, mode: `MaxEncodedLen`)
	fn privatize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `543`
		//  Estimated: `3593`
		// Minimum execution time: 89_467_000 picoseconds.
		Weight::from_parts(92_605_000, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `Nis::Receipts` (r:1 w:1)
	/// Proof: `Nis::Receipts` (`max_values`: None, `max_size`: Some(81), added: 2556, mode: `MaxEncodedLen`)
	/// Storage: `Nis::Summary` (r:1 w:1)
	/// Proof: `Nis::Summary` (`max_values`: Some(1), `max_size`: Some(40), added: 535, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:1)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(103), added: 2578, mode: `MaxEncodedLen`)
	fn thaw_private() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `387`
		//  Estimated: `3593`
		// Minimum execution time: 56_865_000 picoseconds.
		Weight::from_parts(57_749_000, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Nis::Receipts` (r:1 w:1)
	/// Proof: `Nis::Receipts` (`max_values`: None, `max_size`: Some(81), added: 2556, mode: `MaxEncodedLen`)
	/// Storage: `Nis::Summary` (r:1 w:1)
	/// Proof: `Nis::Summary` (`max_values`: Some(1), `max_size`: Some(40), added: 535, mode: `MaxEncodedLen`)
	/// Storage: `NisCounterpartBalances::Account` (r:1 w:1)
	/// Proof: `NisCounterpartBalances::Account` (`max_values`: None, `max_size`: Some(112), added: 2587, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn thaw_communal() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `488`
		//  Estimated: `3593`
		// Minimum execution time: 91_240_000 picoseconds.
		Weight::from_parts(93_106_000, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `Nis::Summary` (r:1 w:1)
	/// Proof: `Nis::Summary` (`max_values`: Some(1), `max_size`: Some(40), added: 535, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Nis::QueueTotals` (r:1 w:1)
	/// Proof: `Nis::QueueTotals` (`max_values`: Some(1), `max_size`: Some(6002), added: 6497, mode: `MaxEncodedLen`)
	fn process_queues() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6658`
		//  Estimated: `7487`
		// Minimum execution time: 23_148_000 picoseconds.
		Weight::from_parts(24_318_000, 0)
			.saturating_add(Weight::from_parts(0, 7487))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Nis::Queues` (r:1 w:1)
	/// Proof: `Nis::Queues` (`max_values`: None, `max_size`: Some(48022), added: 50497, mode: `MaxEncodedLen`)
	fn process_queue() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76`
		//  Estimated: `51487`
		// Minimum execution time: 5_213_000 picoseconds.
		Weight::from_parts(5_487_000, 0)
			.saturating_add(Weight::from_parts(0, 51487))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Nis::Receipts` (r:0 w:1)
	/// Proof: `Nis::Receipts` (`max_values`: None, `max_size`: Some(81), added: 2556, mode: `MaxEncodedLen`)
	fn process_bid() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_226_000 picoseconds.
		Weight::from_parts(5_480_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
