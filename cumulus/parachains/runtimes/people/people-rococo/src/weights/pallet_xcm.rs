// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Autogenerated weights for `pallet_xcm`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `afc679a858d4`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/people-rococo-runtime/people_rococo_runtime.wasm
// --pallet=pallet_xcm
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/people/people-rococo/src/weights
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
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn send() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `75`
		//  Estimated: `3540`
		// Minimum execution time: 24_078_000 picoseconds.
		Weight::from_parts(24_691_000, 0)
			.saturating_add(Weight::from_parts(0, 3540))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `PolkadotXcm::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn teleport_assets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `75`
		//  Estimated: `3540`
		// Minimum execution time: 69_608_000 picoseconds.
		Weight::from_parts(71_370_000, 0)
			.saturating_add(Weight::from_parts(0, 3540))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Benchmark::Override` (r:0 w:0)
	/// Proof: `Benchmark::Override` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn reserve_transfer_assets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 18_446_744_073_709_551_000 picoseconds.
		Weight::from_parts(18_446_744_073_709_551_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	/// Storage: `Benchmark::Override` (r:0 w:0)
	/// Proof: `Benchmark::Override` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn transfer_assets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 18_446_744_073_709_551_000 picoseconds.
		Weight::from_parts(18_446_744_073_709_551_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	/// Storage: `PolkadotXcm::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `PolkadotXcm::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn execute() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `1485`
		// Minimum execution time: 9_722_000 picoseconds.
		Weight::from_parts(10_074_000, 0)
			.saturating_add(Weight::from_parts(0, 1485))
			.saturating_add(T::DbWeight::get().reads(1))
	}
	/// Storage: `PolkadotXcm::SupportedVersion` (r:0 w:1)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn force_xcm_version() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 7_438_000 picoseconds.
		Weight::from_parts(7_681_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	fn force_default_xcm_version() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_561_000 picoseconds.
		Weight::from_parts(2_720_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	/// Storage: `PolkadotXcm::VersionNotifiers` (r:1 w:1)
	/// Proof: `PolkadotXcm::VersionNotifiers` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::QueryCounter` (r:1 w:1)
	/// Proof: `PolkadotXcm::QueryCounter` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::Queries` (r:0 w:1)
	/// Proof: `PolkadotXcm::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn force_subscribe_version_notify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6`
		//  Estimated: `3471`
		// Minimum execution time: 26_808_000 picoseconds.
		Weight::from_parts(27_734_000, 0)
			.saturating_add(Weight::from_parts(0, 3471))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `PolkadotXcm::VersionNotifiers` (r:1 w:1)
	/// Proof: `PolkadotXcm::VersionNotifiers` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::Queries` (r:0 w:1)
	/// Proof: `PolkadotXcm::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn force_unsubscribe_version_notify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `99`
		//  Estimated: `3564`
		// Minimum execution time: 28_560_000 picoseconds.
		Weight::from_parts(29_347_000, 0)
			.saturating_add(Weight::from_parts(0, 3564))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `PolkadotXcm::XcmExecutionSuspended` (r:0 w:1)
	/// Proof: `PolkadotXcm::XcmExecutionSuspended` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn force_suspension() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_548_000 picoseconds.
		Weight::from_parts(2_734_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `PolkadotXcm::SupportedVersion` (r:6 w:2)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn migrate_supported_version() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `23`
		//  Estimated: `15863`
		// Minimum execution time: 20_690_000 picoseconds.
		Weight::from_parts(21_464_000, 0)
			.saturating_add(Weight::from_parts(0, 15863))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `PolkadotXcm::VersionNotifiers` (r:6 w:2)
	/// Proof: `PolkadotXcm::VersionNotifiers` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn migrate_version_notifiers() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `27`
		//  Estimated: `15867`
		// Minimum execution time: 20_931_000 picoseconds.
		Weight::from_parts(21_368_000, 0)
			.saturating_add(Weight::from_parts(0, 15867))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `PolkadotXcm::VersionNotifyTargets` (r:7 w:0)
	/// Proof: `PolkadotXcm::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn already_notified_target() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76`
		//  Estimated: `18391`
		// Minimum execution time: 25_930_000 picoseconds.
		Weight::from_parts(26_340_000, 0)
			.saturating_add(Weight::from_parts(0, 18391))
			.saturating_add(T::DbWeight::get().reads(7))
	}
	/// Storage: `PolkadotXcm::VersionNotifyTargets` (r:2 w:1)
	/// Proof: `PolkadotXcm::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn notify_current_targets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `40`
		//  Estimated: `5980`
		// Minimum execution time: 25_401_000 picoseconds.
		Weight::from_parts(26_305_000, 0)
			.saturating_add(Weight::from_parts(0, 5980))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `PolkadotXcm::VersionNotifyTargets` (r:5 w:0)
	/// Proof: `PolkadotXcm::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn notify_target_migration_fail() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `79`
		//  Estimated: `13444`
		// Minimum execution time: 18_585_000 picoseconds.
		Weight::from_parts(19_031_000, 0)
			.saturating_add(Weight::from_parts(0, 13444))
			.saturating_add(T::DbWeight::get().reads(5))
	}
	/// Storage: `PolkadotXcm::VersionNotifyTargets` (r:6 w:2)
	/// Proof: `PolkadotXcm::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn migrate_version_notify_targets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `34`
		//  Estimated: `15874`
		// Minimum execution time: 20_840_000 picoseconds.
		Weight::from_parts(21_462_000, 0)
			.saturating_add(Weight::from_parts(0, 15874))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `PolkadotXcm::VersionNotifyTargets` (r:6 w:2)
	/// Proof: `PolkadotXcm::VersionNotifyTargets` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn migrate_and_notify_old_targets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `40`
		//  Estimated: `15880`
		// Minimum execution time: 37_906_000 picoseconds.
		Weight::from_parts(38_593_000, 0)
			.saturating_add(Weight::from_parts(0, 15880))
			.saturating_add(T::DbWeight::get().reads(9))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `PolkadotXcm::QueryCounter` (r:1 w:1)
	/// Proof: `PolkadotXcm::QueryCounter` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::Queries` (r:0 w:1)
	/// Proof: `PolkadotXcm::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn new_query() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `1485`
		// Minimum execution time: 2_701_000 picoseconds.
		Weight::from_parts(2_875_000, 0)
			.saturating_add(Weight::from_parts(0, 1485))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `PolkadotXcm::Queries` (r:1 w:1)
	/// Proof: `PolkadotXcm::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn take_response() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7576`
		//  Estimated: `11041`
		// Minimum execution time: 26_329_000 picoseconds.
		Weight::from_parts(26_854_000, 0)
			.saturating_add(Weight::from_parts(0, 11041))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `PolkadotXcm::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `PolkadotXcm::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `PolkadotXcm::AssetTraps` (r:1 w:1)
	/// Proof: `PolkadotXcm::AssetTraps` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn claim_assets() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `24`
		//  Estimated: `3489`
		// Minimum execution time: 39_288_000 picoseconds.
		Weight::from_parts(40_512_000, 0)
			.saturating_add(Weight::from_parts(0, 3489))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
