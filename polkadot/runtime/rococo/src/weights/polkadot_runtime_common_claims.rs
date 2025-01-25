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

//! Autogenerated weights for `polkadot_runtime_common::claims`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `7dc4ae448f59`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot
// benchmark
// pallet
// --extrinsic=*
// --chain=rococo-dev
// --pallet=polkadot_runtime_common::claims
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

/// Weight functions for `polkadot_runtime_common::claims`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> polkadot_runtime_common::claims::WeightInfo for WeightInfo<T> {
	/// Storage: `Claims::Claims` (r:1 w:1)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Signing` (r:1 w:1)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: Some(21), added: 2496, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Total` (r:1 w:1)
	/// Proof: `Claims::Total` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Vesting` (r:1 w:1)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `Vesting::Vesting` (r:1 w:1)
	/// Proof: `Vesting::Vesting` (`max_values`: None, `max_size`: Some(1057), added: 3532, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Locks` (r:1 w:1)
	/// Proof: `Balances::Locks` (`max_values`: None, `max_size`: Some(1299), added: 3774, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Freezes` (r:1 w:0)
	/// Proof: `Balances::Freezes` (`max_values`: None, `max_size`: Some(65), added: 2540, mode: `MaxEncodedLen`)
	fn claim() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `558`
		//  Estimated: `4764`
		// Minimum execution time: 186_145_000 picoseconds.
		Weight::from_parts(205_436_000, 0)
			.saturating_add(Weight::from_parts(0, 4764))
			.saturating_add(T::DbWeight::get().reads(8))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `Claims::Total` (r:1 w:1)
	/// Proof: `Claims::Total` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Vesting` (r:0 w:1)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Claims` (r:0 w:1)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Signing` (r:0 w:1)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: Some(21), added: 2496, mode: `MaxEncodedLen`)
	fn mint_claim() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `216`
		//  Estimated: `1501`
		// Minimum execution time: 15_147_000 picoseconds.
		Weight::from_parts(17_352_000, 0)
			.saturating_add(Weight::from_parts(0, 1501))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `Claims::Claims` (r:1 w:1)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Signing` (r:1 w:1)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: Some(21), added: 2496, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Total` (r:1 w:1)
	/// Proof: `Claims::Total` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Vesting` (r:1 w:1)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `Vesting::Vesting` (r:1 w:1)
	/// Proof: `Vesting::Vesting` (`max_values`: None, `max_size`: Some(1057), added: 3532, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Locks` (r:1 w:1)
	/// Proof: `Balances::Locks` (`max_values`: None, `max_size`: Some(1299), added: 3774, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Freezes` (r:1 w:0)
	/// Proof: `Balances::Freezes` (`max_values`: None, `max_size`: Some(65), added: 2540, mode: `MaxEncodedLen`)
	fn claim_attest() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `558`
		//  Estimated: `4764`
		// Minimum execution time: 203_252_000 picoseconds.
		Weight::from_parts(210_767_000, 0)
			.saturating_add(Weight::from_parts(0, 4764))
			.saturating_add(T::DbWeight::get().reads(8))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `Claims::Preclaims` (r:1 w:1)
	/// Proof: `Claims::Preclaims` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Signing` (r:1 w:1)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: Some(21), added: 2496, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Claims` (r:1 w:1)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Total` (r:1 w:1)
	/// Proof: `Claims::Total` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Vesting` (r:1 w:1)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `Vesting::Vesting` (r:1 w:1)
	/// Proof: `Vesting::Vesting` (`max_values`: None, `max_size`: Some(1057), added: 3532, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Locks` (r:1 w:1)
	/// Proof: `Balances::Locks` (`max_values`: None, `max_size`: Some(1299), added: 3774, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Freezes` (r:1 w:0)
	/// Proof: `Balances::Freezes` (`max_values`: None, `max_size`: Some(65), added: 2540, mode: `MaxEncodedLen`)
	fn attest() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `632`
		//  Estimated: `4764`
		// Minimum execution time: 85_420_000 picoseconds.
		Weight::from_parts(95_354_000, 0)
			.saturating_add(Weight::from_parts(0, 4764))
			.saturating_add(T::DbWeight::get().reads(9))
			.saturating_add(T::DbWeight::get().writes(7))
	}
	/// Storage: `Claims::Claims` (r:1 w:2)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Vesting` (r:1 w:2)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Signing` (r:1 w:2)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: Some(21), added: 2496, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Preclaims` (r:1 w:1)
	/// Proof: `Claims::Preclaims` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	fn move_claim() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `440`
		//  Estimated: `3521`
		// Minimum execution time: 31_817_000 picoseconds.
		Weight::from_parts(34_865_000, 0)
			.saturating_add(Weight::from_parts(0, 3521))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(7))
	}
	/// Storage: `Claims::Preclaims` (r:1 w:0)
	/// Proof: `Claims::Preclaims` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: `Claims::Signing` (r:1 w:0)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: Some(21), added: 2496, mode: `MaxEncodedLen`)
	fn prevalidate_attests() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `296`
		//  Estimated: `3517`
		// Minimum execution time: 11_625_000 picoseconds.
		Weight::from_parts(12_877_000, 0)
			.saturating_add(Weight::from_parts(0, 3517))
			.saturating_add(T::DbWeight::get().reads(2))
	}
}
