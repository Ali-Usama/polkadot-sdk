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

//! Autogenerated weights for `pallet_offences`
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
// --pallet=pallet_offences
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

/// Weight functions for `pallet_offences`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_offences::WeightInfo for WeightInfo<T> {
	/// Storage: `Offences::ConcurrentReportsIndex` (r:1 w:1)
	/// Proof: `Offences::ConcurrentReportsIndex` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Offences::Reports` (r:1 w:1)
	/// Proof: `Offences::Reports` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::SlashRewardFraction` (r:1 w:0)
	/// Proof: `Staking::SlashRewardFraction` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ActiveEra` (r:1 w:0)
	/// Proof: `Staking::ActiveEra` (`max_values`: Some(1), `max_size`: Some(13), added: 508, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStartSessionIndex` (r:1 w:0)
	/// Proof: `Staking::ErasStartSessionIndex` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Invulnerables` (r:1 w:0)
	/// Proof: `Staking::Invulnerables` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ValidatorSlashInEra` (r:1 w:1)
	/// Proof: `Staking::ValidatorSlashInEra` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `Staking::SlashingSpans` (r:17 w:17)
	/// Proof: `Staking::SlashingSpans` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::SpanSlash` (r:17 w:17)
	/// Proof: `Staking::SpanSlash` (`max_values`: None, `max_size`: Some(76), added: 2551, mode: `MaxEncodedLen`)
	/// Storage: `Staking::DisabledValidators` (r:1 w:1)
	/// Proof: `Staking::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::Validators` (r:1 w:0)
	/// Proof: `Session::Validators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::NominatorSlashInEra` (r:16 w:16)
	/// Proof: `Staking::NominatorSlashInEra` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	/// Storage: `Staking::UnappliedSlashes` (r:1 w:1)
	/// Proof: `Staking::UnappliedSlashes` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `n` is `[0, 16]`.
	fn report_offence_grandpa(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `989`
		//  Estimated: `4439 + n * (2551 ±0)`
		// Minimum execution time: 65_000_000 picoseconds.
		Weight::from_parts(69_808_904, 0)
			.saturating_add(Weight::from_parts(0, 4439))
			// Standard Error: 21_948
			.saturating_add(Weight::from_parts(11_767_963, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(12))
			.saturating_add(T::DbWeight::get().reads((3_u64).saturating_mul(n.into())))
			.saturating_add(T::DbWeight::get().writes(7))
			.saturating_add(T::DbWeight::get().writes((3_u64).saturating_mul(n.into())))
			.saturating_add(Weight::from_parts(0, 2551).saturating_mul(n.into()))
	}
	/// Storage: `Offences::ConcurrentReportsIndex` (r:1 w:1)
	/// Proof: `Offences::ConcurrentReportsIndex` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Offences::Reports` (r:1 w:1)
	/// Proof: `Offences::Reports` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::SlashRewardFraction` (r:1 w:0)
	/// Proof: `Staking::SlashRewardFraction` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ActiveEra` (r:1 w:0)
	/// Proof: `Staking::ActiveEra` (`max_values`: Some(1), `max_size`: Some(13), added: 508, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStartSessionIndex` (r:1 w:0)
	/// Proof: `Staking::ErasStartSessionIndex` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Invulnerables` (r:1 w:0)
	/// Proof: `Staking::Invulnerables` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ValidatorSlashInEra` (r:1 w:1)
	/// Proof: `Staking::ValidatorSlashInEra` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `Staking::SlashingSpans` (r:17 w:17)
	/// Proof: `Staking::SlashingSpans` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::SpanSlash` (r:17 w:17)
	/// Proof: `Staking::SpanSlash` (`max_values`: None, `max_size`: Some(76), added: 2551, mode: `MaxEncodedLen`)
	/// Storage: `Staking::DisabledValidators` (r:1 w:1)
	/// Proof: `Staking::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::Validators` (r:1 w:0)
	/// Proof: `Session::Validators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::NominatorSlashInEra` (r:16 w:16)
	/// Proof: `Staking::NominatorSlashInEra` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	/// Storage: `Staking::UnappliedSlashes` (r:1 w:1)
	/// Proof: `Staking::UnappliedSlashes` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `n` is `[0, 16]`.
	fn report_offence_babe(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `989`
		//  Estimated: `4439 + n * (2551 ±0)`
		// Minimum execution time: 65_790_000 picoseconds.
		Weight::from_parts(70_094_005, 0)
			.saturating_add(Weight::from_parts(0, 4439))
			// Standard Error: 26_649
			.saturating_add(Weight::from_parts(11_822_011, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(12))
			.saturating_add(T::DbWeight::get().reads((3_u64).saturating_mul(n.into())))
			.saturating_add(T::DbWeight::get().writes(7))
			.saturating_add(T::DbWeight::get().writes((3_u64).saturating_mul(n.into())))
			.saturating_add(Weight::from_parts(0, 2551).saturating_mul(n.into()))
	}
}
