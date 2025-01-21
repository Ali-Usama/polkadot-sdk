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

//! Autogenerated weights for `pallet_multisig`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `5d8802e9776e`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot
// benchmark
// pallet
// --extrinsic=*
// --chain=rococo-dev
// --pallet=pallet_multisig
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

/// Weight functions for `pallet_multisig`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_multisig::WeightInfo for WeightInfo<T> {
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 16_028_000 picoseconds.
		Weight::from_parts(16_681_633, 0)
			.saturating_add(Weight::from_parts(0, 0))
			// Standard Error: 3
			.saturating_add(Weight::from_parts(494, 0).saturating_mul(z.into()))
	}
	/// Storage: `Multisig::Multisigs` (r:1 w:1)
	/// Proof: `Multisig::Multisigs` (`max_values`: None, `max_size`: Some(3346), added: 5821, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `229 + s * (2 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 47_058_000 picoseconds.
		Weight::from_parts(34_360_911, 0)
			.saturating_add(Weight::from_parts(0, 6811))
			// Standard Error: 1_725
			.saturating_add(Weight::from_parts(143_105, 0).saturating_mul(s.into()))
			// Standard Error: 16
			.saturating_add(Weight::from_parts(2_050, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Multisig::Multisigs` (r:1 w:1)
	/// Proof: `Multisig::Multisigs` (`max_values`: None, `max_size`: Some(3346), added: 5821, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[3, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `248`
		//  Estimated: `6811`
		// Minimum execution time: 31_642_000 picoseconds.
		Weight::from_parts(19_134_832, 0)
			.saturating_add(Weight::from_parts(0, 6811))
			// Standard Error: 1_019
			.saturating_add(Weight::from_parts(130_135, 0).saturating_mul(s.into()))
			// Standard Error: 9
			.saturating_add(Weight::from_parts(2_110, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Multisig::Multisigs` (r:1 w:1)
	/// Proof: `Multisig::Multisigs` (`max_values`: None, `max_size`: Some(3346), added: 5821, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `354 + s * (33 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 51_901_000 picoseconds.
		Weight::from_parts(36_615_267, 0)
			.saturating_add(Weight::from_parts(0, 6811))
			// Standard Error: 1_251
			.saturating_add(Weight::from_parts(171_598, 0).saturating_mul(s.into()))
			// Standard Error: 12
			.saturating_add(Weight::from_parts(2_165, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Multisig::Multisigs` (r:1 w:1)
	/// Proof: `Multisig::Multisigs` (`max_values`: None, `max_size`: Some(3346), added: 5821, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn approve_as_multi_create(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `229 + s * (2 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 30_944_000 picoseconds.
		Weight::from_parts(31_843_902, 0)
			.saturating_add(Weight::from_parts(0, 6811))
			// Standard Error: 958
			.saturating_add(Weight::from_parts(146_314, 0).saturating_mul(s.into()))
			// Standard Error: 9
			.saturating_add(Weight::from_parts(86, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Multisig::Multisigs` (r:1 w:1)
	/// Proof: `Multisig::Multisigs` (`max_values`: None, `max_size`: Some(3346), added: 5821, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn approve_as_multi_approve(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `248`
		//  Estimated: `6811`
		// Minimum execution time: 16_922_000 picoseconds.
		Weight::from_parts(18_273_526, 0)
			.saturating_add(Weight::from_parts(0, 6811))
			// Standard Error: 974
			.saturating_add(Weight::from_parts(125_923, 0).saturating_mul(s.into()))
			// Standard Error: 9
			.saturating_add(Weight::from_parts(22, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Multisig::Multisigs` (r:1 w:1)
	/// Proof: `Multisig::Multisigs` (`max_values`: None, `max_size`: Some(3346), added: 5821, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn cancel_as_multi(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `420 + s * (1 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 32_084_000 picoseconds.
		Weight::from_parts(33_640_455, 0)
			.saturating_add(Weight::from_parts(0, 6811))
			// Standard Error: 967
			.saturating_add(Weight::from_parts(133_992, 0).saturating_mul(s.into()))
			// Standard Error: 9
			.saturating_add(Weight::from_parts(22, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
