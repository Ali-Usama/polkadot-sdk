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

//! Autogenerated weights for `pallet_migrations`
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
// --pallet=pallet_migrations
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

/// Weight functions for `pallet_migrations`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_migrations::WeightInfo for WeightInfo<T> {
	/// Storage: `MultiBlockMigrations::Cursor` (r:1 w:1)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	fn onboard_new_mbms() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `100`
		//  Estimated: `67035`
		// Minimum execution time: 8_286_000 picoseconds.
		Weight::from_parts(8_812_000, 0)
			.saturating_add(Weight::from_parts(0, 67035))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MultiBlockMigrations::Cursor` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	fn progress_mbms_none() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4`
		//  Estimated: `67035`
		// Minimum execution time: 2_036_000 picoseconds.
		Weight::from_parts(2_126_000, 0)
			.saturating_add(Weight::from_parts(0, 67035))
			.saturating_add(T::DbWeight::get().reads(1))
	}
	/// Storage: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Storage: `MultiBlockMigrations::Cursor` (r:0 w:1)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	fn exec_migration_completed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `96`
		//  Estimated: `3561`
		// Minimum execution time: 6_637_000 picoseconds.
		Weight::from_parts(6_962_000, 0)
			.saturating_add(Weight::from_parts(0, 3561))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Storage: `MultiBlockMigrations::Historic` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Historic` (`max_values`: None, `max_size`: Some(266), added: 2741, mode: `MaxEncodedLen`)
	fn exec_migration_skipped_historic() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `154`
		//  Estimated: `3731`
		// Minimum execution time: 11_769_000 picoseconds.
		Weight::from_parts(12_397_000, 0)
			.saturating_add(Weight::from_parts(0, 3731))
			.saturating_add(T::DbWeight::get().reads(2))
	}
	/// Storage: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Storage: `MultiBlockMigrations::Historic` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Historic` (`max_values`: None, `max_size`: Some(266), added: 2741, mode: `MaxEncodedLen`)
	fn exec_migration_advance() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `100`
		//  Estimated: `3731`
		// Minimum execution time: 11_118_000 picoseconds.
		Weight::from_parts(11_422_000, 0)
			.saturating_add(Weight::from_parts(0, 3731))
			.saturating_add(T::DbWeight::get().reads(2))
	}
	/// Storage: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Storage: `MultiBlockMigrations::Historic` (r:1 w:1)
	/// Proof: `MultiBlockMigrations::Historic` (`max_values`: None, `max_size`: Some(266), added: 2741, mode: `MaxEncodedLen`)
	fn exec_migration_complete() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `100`
		//  Estimated: `3731`
		// Minimum execution time: 12_498_000 picoseconds.
		Weight::from_parts(13_179_000, 0)
			.saturating_add(Weight::from_parts(0, 3731))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Storage: `MultiBlockMigrations::Historic` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Historic` (`max_values`: None, `max_size`: Some(266), added: 2741, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockMigrations::Cursor` (r:0 w:1)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	fn exec_migration_fail() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `100`
		//  Estimated: `3731`
		// Minimum execution time: 13_733_000 picoseconds.
		Weight::from_parts(14_396_000, 0)
			.saturating_add(Weight::from_parts(0, 3731))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	fn on_init_loop() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 186_000 picoseconds.
		Weight::from_parts(221_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	/// Storage: `MultiBlockMigrations::Cursor` (r:0 w:1)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	fn force_set_cursor() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_907_000 picoseconds.
		Weight::from_parts(3_008_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MultiBlockMigrations::Cursor` (r:0 w:1)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	fn force_set_active_cursor() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 3_221_000 picoseconds.
		Weight::from_parts(3_482_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MultiBlockMigrations::Cursor` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x583359fe0e84d953a9dd84e8addb08a5` (r:1 w:0)
	fn force_onboard_mbms() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76`
		//  Estimated: `67035`
		// Minimum execution time: 5_924_000 picoseconds.
		Weight::from_parts(6_136_000, 0)
			.saturating_add(Weight::from_parts(0, 67035))
			.saturating_add(T::DbWeight::get().reads(2))
	}
	/// Storage: `MultiBlockMigrations::Historic` (r:256 w:256)
	/// Proof: `MultiBlockMigrations::Historic` (`max_values`: None, `max_size`: Some(266), added: 2741, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 256]`.
	fn clear_historic(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `984 + n * (271 ±0)`
		//  Estimated: `3834 + n * (2740 ±0)`
		// Minimum execution time: 16_503_000 picoseconds.
		Weight::from_parts(14_436_676, 0)
			.saturating_add(Weight::from_parts(0, 3834))
			// Standard Error: 2_931
			.saturating_add(Weight::from_parts(1_456_205, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(n.into())))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(n.into())))
			.saturating_add(Weight::from_parts(0, 2740).saturating_mul(n.into()))
	}
}
