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

//! Autogenerated weights for `pallet_xcm`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-20, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `774e23c04fca`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot
// benchmark
// pallet
// --extrinsic=*
// --chain=rococo-dev
// --pallet=pallet_xcm
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

/// Weight functions for `pallet_xcm`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_xcm::WeightInfo for WeightInfo<T> {
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
	fn send() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `245`
		//  Estimated: `3710`
		// Minimum execution time: 38_152_000 picoseconds.
		Weight::from_parts(39_523_000, 0)
			.saturating_add(Weight::from_parts(0, 3710))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `XcmPallet::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `XcmPallet::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
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
	fn teleport_assets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `245`
		//  Estimated: `3710`
		// Minimum execution time: 142_363_000 picoseconds.
		Weight::from_parts(146_493_000, 0)
			.saturating_add(Weight::from_parts(0, 3710))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `XcmPallet::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `XcmPallet::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::Account` (r:1 w:1)
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
	fn reserve_transfer_assets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `297`
		//  Estimated: `3762`
		// Minimum execution time: 140_553_000 picoseconds.
		Weight::from_parts(144_900_000, 0)
			.saturating_add(Weight::from_parts(0, 3762))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `XcmPallet::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `XcmPallet::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
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
	fn transfer_assets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `245`
		//  Estimated: `3710`
		// Minimum execution time: 145_482_000 picoseconds.
		Weight::from_parts(148_203_000, 0)
			.saturating_add(Weight::from_parts(0, 3710))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `XcmPallet::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `XcmPallet::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn execute() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `1485`
		// Minimum execution time: 10_146_000 picoseconds.
		Weight::from_parts(10_622_000, 0)
			.saturating_add(Weight::from_parts(0, 1485))
			.saturating_add(T::DbWeight::get().reads(1))
	}
	/// Storage: `XcmPallet::SupportedVersion` (r:0 w:1)
	/// Proof: `XcmPallet::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn force_xcm_version() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 8_483_000 picoseconds.
		Weight::from_parts(9_051_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	fn force_default_xcm_version() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_511_000 picoseconds.
		Weight::from_parts(2_658_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	/// Storage: `XcmPallet::VersionNotifiers` (r:1 w:1)
	/// Proof: `XcmPallet::VersionNotifiers` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `XcmPallet::QueryCounter` (r:1 w:1)
	/// Proof: `XcmPallet::QueryCounter` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
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
	/// Storage: `XcmPallet::Queries` (r:0 w:1)
	/// Proof: `XcmPallet::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn force_subscribe_version_notify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `245`
		//  Estimated: `3710`
		// Minimum execution time: 46_219_000 picoseconds.
		Weight::from_parts(48_314_000, 0)
			.saturating_add(Weight::from_parts(0, 3710))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `XcmPallet::VersionNotifiers` (r:1 w:1)
	/// Proof: `XcmPallet::VersionNotifiers` (`max_values`: None, `max_size`: None, mode: `Measured`)
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
	/// Storage: `XcmPallet::Queries` (r:0 w:1)
	/// Proof: `XcmPallet::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn force_unsubscribe_version_notify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `425`
		//  Estimated: `3890`
		// Minimum execution time: 50_639_000 picoseconds.
		Weight::from_parts(52_151_000, 0)
			.saturating_add(Weight::from_parts(0, 3890))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `XcmPallet::XcmExecutionSuspended` (r:0 w:1)
	/// Proof: `XcmPallet::XcmExecutionSuspended` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn force_suspension() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_372_000 picoseconds.
		Weight::from_parts(2_621_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `XcmPallet::SupportedVersion` (r:6 w:2)
	/// Proof: `XcmPallet::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn migrate_supported_version() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `22`
		//  Estimated: `15862`
		// Minimum execution time: 21_935_000 picoseconds.
		Weight::from_parts(22_426_000, 0)
			.saturating_add(Weight::from_parts(0, 15862))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `XcmPallet::VersionNotifiers` (r:6 w:2)
	/// Proof: `XcmPallet::VersionNotifiers` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn migrate_version_notifiers() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `26`
		//  Estimated: `15866`
		// Minimum execution time: 22_009_000 picoseconds.
		Weight::from_parts(22_846_000, 0)
			.saturating_add(Weight::from_parts(0, 15866))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `XcmPallet::VersionNotifyTargets` (r:7 w:0)
	/// Proof: `XcmPallet::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn already_notified_target() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `40`
		//  Estimated: `18355`
		// Minimum execution time: 25_580_000 picoseconds.
		Weight::from_parts(26_106_000, 0)
			.saturating_add(Weight::from_parts(0, 18355))
			.saturating_add(T::DbWeight::get().reads(7))
	}
	/// Storage: `XcmPallet::VersionNotifyTargets` (r:2 w:1)
	/// Proof: `XcmPallet::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DeliveryFeeFactor` (r:1 w:0)
	/// Proof: `Dmp::DeliveryFeeFactor` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `XcmPallet::SupportedVersion` (r:1 w:0)
	/// Proof: `XcmPallet::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DownwardMessageQueues` (r:1 w:0)
	/// Proof: `Dmp::DownwardMessageQueues` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::Heads` (r:1 w:0)
	/// Proof: `Paras::Heads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn notify_current_targets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `244`
		//  Estimated: `6184`
		// Minimum execution time: 33_058_000 picoseconds.
		Weight::from_parts(34_215_000, 0)
			.saturating_add(Weight::from_parts(0, 6184))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `XcmPallet::VersionNotifyTargets` (r:5 w:0)
	/// Proof: `XcmPallet::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn notify_target_migration_fail() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `40`
		//  Estimated: `13405`
		// Minimum execution time: 17_198_000 picoseconds.
		Weight::from_parts(17_543_000, 0)
			.saturating_add(Weight::from_parts(0, 13405))
			.saturating_add(T::DbWeight::get().reads(5))
	}
	/// Storage: `XcmPallet::VersionNotifyTargets` (r:6 w:2)
	/// Proof: `XcmPallet::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn migrate_version_notify_targets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `33`
		//  Estimated: `15873`
		// Minimum execution time: 21_697_000 picoseconds.
		Weight::from_parts(22_375_000, 0)
			.saturating_add(Weight::from_parts(0, 15873))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `XcmPallet::VersionNotifyTargets` (r:6 w:1)
	/// Proof: `XcmPallet::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DeliveryFeeFactor` (r:1 w:0)
	/// Proof: `Dmp::DeliveryFeeFactor` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `XcmPallet::SupportedVersion` (r:1 w:0)
	/// Proof: `XcmPallet::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DownwardMessageQueues` (r:1 w:0)
	/// Proof: `Dmp::DownwardMessageQueues` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::Heads` (r:1 w:0)
	/// Proof: `Paras::Heads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn migrate_and_notify_old_targets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `244`
		//  Estimated: `16084`
		// Minimum execution time: 43_970_000 picoseconds.
		Weight::from_parts(45_097_000, 0)
			.saturating_add(Weight::from_parts(0, 16084))
			.saturating_add(T::DbWeight::get().reads(10))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `XcmPallet::QueryCounter` (r:1 w:1)
	/// Proof: `XcmPallet::QueryCounter` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `XcmPallet::Queries` (r:0 w:1)
	/// Proof: `XcmPallet::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn new_query() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `1485`
		// Minimum execution time: 2_751_000 picoseconds.
		Weight::from_parts(2_897_000, 0)
			.saturating_add(Weight::from_parts(0, 1485))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `XcmPallet::Queries` (r:1 w:1)
	/// Proof: `XcmPallet::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn take_response() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7576`
		//  Estimated: `11041`
		// Minimum execution time: 26_450_000 picoseconds.
		Weight::from_parts(26_962_000, 0)
			.saturating_add(Weight::from_parts(0, 11041))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `XcmPallet::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `XcmPallet::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `XcmPallet::AssetTraps` (r:1 w:1)
	/// Proof: `XcmPallet::AssetTraps` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn claim_assets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `23`
		//  Estimated: `3488`
		// Minimum execution time: 41_151_000 picoseconds.
		Weight::from_parts(42_581_000, 0)
			.saturating_add(Weight::from_parts(0, 3488))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
