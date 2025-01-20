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

//! Autogenerated weights for `polkadot_runtime_parachains::coretime`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-20, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `11a45f968ffa`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot
// benchmark
// pallet
// --extrinsic=*
// --chain=westend-dev
// --pallet=polkadot_runtime_parachains::coretime
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

/// Weight functions for `polkadot_runtime_parachains::coretime`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> polkadot_runtime_parachains::coretime::WeightInfo for WeightInfo<T> {
	/// Storage: `OnDemandAssignmentProvider::Revenue` (r:1 w:1)
	/// Proof: `OnDemandAssignmentProvider::Revenue` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Dmp::DeliveryFeeFactor` (r:1 w:0)
	/// Proof: `Dmp::DeliveryFeeFactor` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `XcmPallet::SupportedVersion` (r:1 w:0)
	/// Proof: `XcmPallet::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DownwardMessageQueues` (r:1 w:1)
	/// Proof: `Dmp::DownwardMessageQueues` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::Heads` (r:1 w:0)
	/// Proof: `Paras::Heads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DownwardMessageQueueHeads` (r:1 w:1)
	/// Proof: `Dmp::DownwardMessageQueueHeads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn request_revenue_at() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `3083`
		//  Estimated: `6548`
		// Minimum execution time: 98_694_000 picoseconds.
		Weight::from_parts(102_369_000, 0)
			.saturating_add(Weight::from_parts(0, 6548))
			.saturating_add(T::DbWeight::get().reads(8))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `Configuration::PendingConfigs` (r:1 w:1)
	/// Proof: `Configuration::PendingConfigs` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Configuration::BypassConsistencyCheck` (r:1 w:0)
	/// Proof: `Configuration::BypassConsistencyCheck` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn request_core_count() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `151`
		//  Estimated: `1636`
		// Minimum execution time: 10_813_000 picoseconds.
		Weight::from_parts(11_074_000, 0)
			.saturating_add(Weight::from_parts(0, 1636))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `CoretimeAssignmentProvider::CoreDescriptors` (r:1 w:1)
	/// Proof: `CoretimeAssignmentProvider::CoreDescriptors` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `CoretimeAssignmentProvider::CoreSchedules` (r:0 w:1)
	/// Proof: `CoretimeAssignmentProvider::CoreSchedules` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `s` is `[1, 100]`.
	fn assign_core(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `147`
		//  Estimated: `3612`
		// Minimum execution time: 15_449_000 picoseconds.
		Weight::from_parts(16_231_640, 0)
			.saturating_add(Weight::from_parts(0, 3612))
			// Standard Error: 392
			.saturating_add(Weight::from_parts(14_062, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(2))
	}
}
