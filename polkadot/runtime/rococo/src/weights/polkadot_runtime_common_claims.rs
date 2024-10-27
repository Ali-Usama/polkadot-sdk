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

//! Autogenerated weights for `runtime_common::claims`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2024-02-29, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-bn-ce5rx-project-674-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("rococo-dev")`, DB CACHE: 1024

// Executed Command:
// ./target/production/polkadot
// benchmark
// pallet
// --chain=rococo-dev
// --steps=50
// --repeat=20
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --pallet=runtime_common::claims
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --header=./polkadot/file_header.txt
// --output=./polkadot/runtime/rococo/src/weights/runtime_common_claims.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::Weight};
use core::marker::PhantomData;

/// Weight functions for `runtime_common::claims`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> polkadot_runtime_common::claims::WeightInfo for WeightInfo<T> {
	/// Storage: Claims Claims (r:1 w:1)
	/// Proof Skipped: Claims Claims (max_values: None, max_size: None, mode: Measured)
	/// Storage: Claims Signing (r:1 w:1)
	/// Proof Skipped: Claims Signing (max_values: None, max_size: None, mode: Measured)
	/// Storage: Claims Total (r:1 w:1)
	/// Proof Skipped: Claims Total (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Claims Vesting (r:1 w:1)
	/// Proof Skipped: Claims Vesting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Vesting Vesting (r:1 w:1)
	/// Proof: Vesting Vesting (max_values: None, max_size: Some(1057), added: 3532, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:0)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// Storage: Balances Freezes (r:1 w:0)
	/// Proof: Balances Freezes (max_values: None, max_size: Some(65), added: 2540, mode: MaxEncodedLen)
	fn claim() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `558`
		//  Estimated: `4764`
		// Minimum execution time: 181_028_000 picoseconds.
		Weight::from_parts(194_590_000, 0)
			.saturating_add(Weight::from_parts(0, 4764))
			.saturating_add(T::DbWeight::get().reads(8))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `Claims::Total` (r:1 w:1)
	/// Proof: `Claims::Total` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Vesting` (r:0 w:1)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Claims` (r:0 w:1)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Signing` (r:0 w:1)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn mint_claim() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `216`
		//  Estimated: `1701`
		// Minimum execution time: 11_224_000 picoseconds.
		Weight::from_parts(13_342_000, 0)
			.saturating_add(Weight::from_parts(0, 1701))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `Claims::Claims` (r:1 w:1)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Signing` (r:1 w:1)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Total` (r:1 w:1)
	/// Proof: `Claims::Total` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Vesting` (r:1 w:1)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: None, mode: `Measured`)
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
		// Minimum execution time: 187_964_000 picoseconds.
		Weight::from_parts(202_553_000, 0)
			.saturating_add(Weight::from_parts(0, 4764))
			.saturating_add(T::DbWeight::get().reads(8))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `Claims::Preclaims` (r:1 w:1)
	/// Proof: `Claims::Preclaims` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Signing` (r:1 w:1)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Claims` (r:1 w:1)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Total` (r:1 w:1)
	/// Proof: `Claims::Total` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Vesting` (r:1 w:1)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: None, mode: `Measured`)
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
		// Minimum execution time: 78_210_000 picoseconds.
		Weight::from_parts(84_581_000, 0)
			.saturating_add(Weight::from_parts(0, 4764))
			.saturating_add(T::DbWeight::get().reads(9))
			.saturating_add(T::DbWeight::get().writes(7))
	}
	/// Storage: `Claims::Claims` (r:1 w:2)
	/// Proof: `Claims::Claims` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Vesting` (r:1 w:2)
	/// Proof: `Claims::Vesting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Signing` (r:1 w:2)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Preclaims` (r:1 w:1)
	/// Proof: `Claims::Preclaims` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn move_claim() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `440`
		//  Estimated: `3905`
		// Minimum execution time: 33_940_000 picoseconds.
		Weight::from_parts(48_438_000, 0)
			.saturating_add(Weight::from_parts(0, 3905))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(7))
	}
	/// Storage: `Claims::Preclaims` (r:1 w:0)
	/// Proof: `Claims::Preclaims` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Claims::Signing` (r:1 w:0)
	/// Proof: `Claims::Signing` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn prevalidate_attests() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `296`
		//  Estimated: `3761`
		// Minimum execution time: 9_025_000 picoseconds.
		Weight::from_parts(10_563_000, 0)
			.saturating_add(Weight::from_parts(0, 3761))
			.saturating_add(T::DbWeight::get().reads(2))
	}
	fn claim_general() -> Weight {
		Weight::zero()
	}
	fn claim_attest_general() -> Weight {
		Weight::zero()
	}
	fn authorize_claim_general() -> Weight {
		Weight::zero()
	}
	fn authorize_claim_attest_general() -> Weight {
		Weight::zero()
	}
}
