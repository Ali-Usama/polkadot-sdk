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

//! Autogenerated weights for `pallet_broker`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `731f893ee36e`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/coretime-rococo-runtime/coretime_rococo_runtime.wasm
// --pallet=pallet_broker
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/coretime/coretime-rococo/src/weights
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

/// Weight functions for `pallet_broker`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_broker::WeightInfo for WeightInfo<T> {
	/// Storage: `Broker::Configuration` (r:0 w:1)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	fn configure() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_559_000 picoseconds.
		Weight::from_parts(2_723_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Reservations` (r:1 w:1)
	/// Proof: `Broker::Reservations` (`max_values`: Some(1), `max_size`: Some(12021), added: 12516, mode: `MaxEncodedLen`)
	fn reserve() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `10888`
		//  Estimated: `13506`
		// Minimum execution time: 25_270_000 picoseconds.
		Weight::from_parts(28_036_000, 0)
			.saturating_add(Weight::from_parts(0, 13506))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Reservations` (r:1 w:1)
	/// Proof: `Broker::Reservations` (`max_values`: Some(1), `max_size`: Some(12021), added: 12516, mode: `MaxEncodedLen`)
	fn unreserve() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `12090`
		//  Estimated: `13506`
		// Minimum execution time: 25_774_000 picoseconds.
		Weight::from_parts(26_297_000, 0)
			.saturating_add(Weight::from_parts(0, 13506))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Leases` (r:1 w:1)
	/// Proof: `Broker::Leases` (`max_values`: Some(1), `max_size`: Some(401), added: 896, mode: `MaxEncodedLen`)
	/// Storage: `ParachainSystem::ValidationData` (r:1 w:0)
	/// Proof: `ParachainSystem::ValidationData` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::LastRelayChainBlockNumber` (r:1 w:0)
	/// Proof: `ParachainSystem::LastRelayChainBlockNumber` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn set_lease() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `466`
		//  Estimated: `1951`
		// Minimum execution time: 13_685_000 picoseconds.
		Weight::from_parts(14_628_000, 0)
			.saturating_add(Weight::from_parts(0, 1951))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Leases` (r:1 w:1)
	/// Proof: `Broker::Leases` (`max_values`: Some(1), `max_size`: Some(401), added: 896, mode: `MaxEncodedLen`)
	fn remove_lease() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `470`
		//  Estimated: `1886`
		// Minimum execution time: 10_681_000 picoseconds.
		Weight::from_parts(11_120_000, 0)
			.saturating_add(Weight::from_parts(0, 1886))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Configuration` (r:1 w:0)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Leases` (r:1 w:1)
	/// Proof: `Broker::Leases` (`max_values`: Some(1), `max_size`: Some(401), added: 896, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Reservations` (r:1 w:0)
	/// Proof: `Broker::Reservations` (`max_values`: Some(1), `max_size`: Some(12021), added: 12516, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::ValidationData` (r:1 w:0)
	/// Proof: `ParachainSystem::ValidationData` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::LastRelayChainBlockNumber` (r:1 w:0)
	/// Proof: `ParachainSystem::LastRelayChainBlockNumber` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Broker::InstaPoolIo` (r:3 w:3)
	/// Proof: `Broker::InstaPoolIo` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `Broker::AutoRenewals` (r:1 w:1)
	/// Proof: `Broker::AutoRenewals` (`max_values`: Some(1), `max_size`: Some(1002), added: 1497, mode: `MaxEncodedLen`)
	/// Storage: `Broker::SaleInfo` (r:0 w:1)
	/// Proof: `Broker::SaleInfo` (`max_values`: Some(1), `max_size`: Some(57), added: 552, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Status` (r:0 w:1)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Workplan` (r:0 w:60)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 1000]`.
	fn start_sales(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `12567`
		//  Estimated: `15033 + n * (1 ±0)`
		// Minimum execution time: 51_814_000 picoseconds.
		Weight::from_parts(150_721_297, 0)
			.saturating_add(Weight::from_parts(0, 15033))
			// Standard Error: 2_705
			.saturating_add(Weight::from_parts(20_778, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(12))
			.saturating_add(T::DbWeight::get().writes(59))
			.saturating_add(Weight::from_parts(0, 1).saturating_mul(n.into()))
	}
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::SaleInfo` (r:1 w:1)
	/// Proof: `Broker::SaleInfo` (`max_values`: Some(1), `max_size`: Some(57), added: 552, mode: `MaxEncodedLen`)
	/// Storage: `ParachainSystem::ValidationData` (r:1 w:0)
	/// Proof: `ParachainSystem::ValidationData` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Regions` (r:0 w:1)
	/// Proof: `Broker::Regions` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	fn purchase() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `437`
		//  Estimated: `3593`
		// Minimum execution time: 64_403_000 picoseconds.
		Weight::from_parts(69_856_000, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Broker::Configuration` (r:1 w:0)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::SaleInfo` (r:1 w:1)
	/// Proof: `Broker::SaleInfo` (`max_values`: Some(1), `max_size`: Some(57), added: 552, mode: `MaxEncodedLen`)
	/// Storage: `Broker::PotentialRenewals` (r:1 w:2)
	/// Proof: `Broker::PotentialRenewals` (`max_values`: None, `max_size`: Some(1233), added: 3708, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ParachainSystem::ValidationData` (r:1 w:0)
	/// Proof: `ParachainSystem::ValidationData` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Broker::Workplan` (r:0 w:1)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	fn renew() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `658`
		//  Estimated: `4698`
		// Minimum execution time: 117_679_000 picoseconds.
		Weight::from_parts(131_097_000, 0)
			.saturating_add(Weight::from_parts(0, 4698))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `Broker::Regions` (r:1 w:1)
	/// Proof: `Broker::Regions` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	fn transfer() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `358`
		//  Estimated: `3551`
		// Minimum execution time: 21_875_000 picoseconds.
		Weight::from_parts(23_688_000, 0)
			.saturating_add(Weight::from_parts(0, 3551))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Regions` (r:1 w:2)
	/// Proof: `Broker::Regions` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	fn partition() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `358`
		//  Estimated: `3551`
		// Minimum execution time: 23_879_000 picoseconds.
		Weight::from_parts(25_354_000, 0)
			.saturating_add(Weight::from_parts(0, 3551))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Broker::Regions` (r:1 w:3)
	/// Proof: `Broker::Regions` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	fn interlace() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `358`
		//  Estimated: `3551`
		// Minimum execution time: 25_199_000 picoseconds.
		Weight::from_parts(29_209_000, 0)
			.saturating_add(Weight::from_parts(0, 3551))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Broker::Configuration` (r:1 w:0)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Regions` (r:1 w:1)
	/// Proof: `Broker::Regions` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Workplan` (r:1 w:1)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	fn assign() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `937`
		//  Estimated: `4681`
		// Minimum execution time: 38_377_000 picoseconds.
		Weight::from_parts(41_124_000, 0)
			.saturating_add(Weight::from_parts(0, 4681))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Regions` (r:1 w:1)
	/// Proof: `Broker::Regions` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Workplan` (r:1 w:1)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	/// Storage: `Broker::InstaPoolIo` (r:2 w:2)
	/// Proof: `Broker::InstaPoolIo` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `Broker::InstaPoolContribution` (r:0 w:1)
	/// Proof: `Broker::InstaPoolContribution` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	fn pool() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1003`
		//  Estimated: `5996`
		// Minimum execution time: 45_084_000 picoseconds.
		Weight::from_parts(46_851_000, 0)
			.saturating_add(Weight::from_parts(0, 5996))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `Broker::InstaPoolContribution` (r:1 w:1)
	/// Proof: `Broker::InstaPoolContribution` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	/// Storage: `Broker::InstaPoolHistory` (r:3 w:1)
	/// Proof: `Broker::InstaPoolHistory` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `m` is `[1, 3]`.
	fn claim_revenue(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `671`
		//  Estimated: `6196 + m * (2520 ±0)`
		// Minimum execution time: 72_975_000 picoseconds.
		Weight::from_parts(76_716_241, 0)
			.saturating_add(Weight::from_parts(0, 6196))
			// Standard Error: 159_873
			.saturating_add(Weight::from_parts(1_699_650, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(m.into())))
			.saturating_add(T::DbWeight::get().writes(5))
			.saturating_add(Weight::from_parts(0, 2520).saturating_mul(m.into()))
	}
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn purchase_credit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `261`
		//  Estimated: `3726`
		// Minimum execution time: 73_412_000 picoseconds.
		Weight::from_parts(77_554_000, 0)
			.saturating_add(Weight::from_parts(0, 3726))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Regions` (r:1 w:1)
	/// Proof: `Broker::Regions` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	fn drop_region() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `466`
		//  Estimated: `3551`
		// Minimum execution time: 62_820_000 picoseconds.
		Weight::from_parts(85_149_000, 0)
			.saturating_add(Weight::from_parts(0, 3551))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Configuration` (r:1 w:0)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::InstaPoolContribution` (r:1 w:1)
	/// Proof: `Broker::InstaPoolContribution` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	fn drop_contribution() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `463`
		//  Estimated: `3533`
		// Minimum execution time: 104_501_000 picoseconds.
		Weight::from_parts(146_124_000, 0)
			.saturating_add(Weight::from_parts(0, 3533))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Configuration` (r:1 w:0)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::InstaPoolHistory` (r:1 w:1)
	/// Proof: `Broker::InstaPoolHistory` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn drop_history() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `979`
		//  Estimated: `3593`
		// Minimum execution time: 132_420_000 picoseconds.
		Weight::from_parts(176_072_000, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::PotentialRenewals` (r:1 w:1)
	/// Proof: `Broker::PotentialRenewals` (`max_values`: None, `max_size`: Some(1233), added: 3708, mode: `MaxEncodedLen`)
	fn drop_renewal() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `957`
		//  Estimated: `4698`
		// Minimum execution time: 67_350_000 picoseconds.
		Weight::from_parts(84_436_000, 0)
			.saturating_add(Weight::from_parts(0, 4698))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `n` is `[0, 1000]`.
	fn request_core_count(_n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `42`
		//  Estimated: `3507`
		// Minimum execution time: 21_143_000 picoseconds.
		Weight::from_parts(22_691_546, 0)
			.saturating_add(Weight::from_parts(0, 3507))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::CoreCountInbox` (r:1 w:1)
	/// Proof: `Broker::CoreCountInbox` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 1000]`.
	fn process_core_count(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `266`
		//  Estimated: `1487`
		// Minimum execution time: 7_972_000 picoseconds.
		Weight::from_parts(8_929_699, 0)
			.saturating_add(Weight::from_parts(0, 1487))
			// Standard Error: 44
			.saturating_add(Weight::from_parts(145, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::RevenueInbox` (r:1 w:1)
	/// Proof: `Broker::RevenueInbox` (`max_values`: Some(1), `max_size`: Some(20), added: 515, mode: `MaxEncodedLen`)
	/// Storage: `Broker::InstaPoolHistory` (r:1 w:1)
	/// Proof: `Broker::InstaPoolHistory` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn process_revenue() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `461`
		//  Estimated: `6196`
		// Minimum execution time: 58_860_000 picoseconds.
		Weight::from_parts(63_100_000, 0)
			.saturating_add(Weight::from_parts(0, 6196))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `ParachainSystem::ValidationData` (r:1 w:0)
	/// Proof: `ParachainSystem::ValidationData` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Broker::InstaPoolIo` (r:3 w:3)
	/// Proof: `Broker::InstaPoolIo` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Reservations` (r:1 w:0)
	/// Proof: `Broker::Reservations` (`max_values`: Some(1), `max_size`: Some(12021), added: 12516, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Leases` (r:1 w:1)
	/// Proof: `Broker::Leases` (`max_values`: Some(1), `max_size`: Some(401), added: 896, mode: `MaxEncodedLen`)
	/// Storage: `Broker::AutoRenewals` (r:1 w:1)
	/// Proof: `Broker::AutoRenewals` (`max_values`: Some(1), `max_size`: Some(1002), added: 1497, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Configuration` (r:1 w:0)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::PotentialRenewals` (r:100 w:200)
	/// Proof: `Broker::PotentialRenewals` (`max_values`: None, `max_size`: Some(1233), added: 3708, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:101 w:101)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Broker::SaleInfo` (r:0 w:1)
	/// Proof: `Broker::SaleInfo` (`max_values`: Some(1), `max_size`: Some(57), added: 552, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Workplan` (r:0 w:1000)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 1000]`.
	fn rotate_sale(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `32497`
		//  Estimated: `233641 + n * (198 ±9)`
		// Minimum execution time: 32_268_000 picoseconds.
		Weight::from_parts(2_840_705_550, 0)
			.saturating_add(Weight::from_parts(0, 233641))
			// Standard Error: 173_120
			.saturating_add(Weight::from_parts(4_374_189, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(126))
			.saturating_add(T::DbWeight::get().writes(181))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(n.into())))
			.saturating_add(Weight::from_parts(0, 198).saturating_mul(n.into()))
	}
	/// Storage: `Broker::InstaPoolIo` (r:1 w:0)
	/// Proof: `Broker::InstaPoolIo` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `Broker::InstaPoolHistory` (r:0 w:1)
	/// Proof: `Broker::InstaPoolHistory` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	fn process_pool() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `42`
		//  Estimated: `3493`
		// Minimum execution time: 7_959_000 picoseconds.
		Weight::from_parts(8_480_000, 0)
			.saturating_add(Weight::from_parts(0, 3493))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Workplan` (r:1 w:1)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Workload` (r:1 w:1)
	/// Proof: `Broker::Workload` (`max_values`: None, `max_size`: Some(1212), added: 3687, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn process_core_schedule() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1289`
		//  Estimated: `4754`
		// Minimum execution time: 32_507_000 picoseconds.
		Weight::from_parts(33_752_000, 0)
			.saturating_add(Weight::from_parts(0, 4754))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn request_revenue_info_at() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `42`
		//  Estimated: `3507`
		// Minimum execution time: 16_470_000 picoseconds.
		Weight::from_parts(17_120_000, 0)
			.saturating_add(Weight::from_parts(0, 3507))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::CoreCountInbox` (r:0 w:1)
	/// Proof: `Broker::CoreCountInbox` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	fn notify_core_count() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_503_000 picoseconds.
		Weight::from_parts(2_674_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::RevenueInbox` (r:0 w:1)
	/// Proof: `Broker::RevenueInbox` (`max_values`: Some(1), `max_size`: Some(20), added: 515, mode: `MaxEncodedLen`)
	fn notify_revenue() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_519_000 picoseconds.
		Weight::from_parts(2_752_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::Status` (r:1 w:1)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Configuration` (r:1 w:0)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	/// Storage: `Broker::CoreCountInbox` (r:1 w:0)
	/// Proof: `Broker::CoreCountInbox` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `Broker::RevenueInbox` (r:1 w:0)
	/// Proof: `Broker::RevenueInbox` (`max_values`: Some(1), `max_size`: Some(20), added: 515, mode: `MaxEncodedLen`)
	/// Storage: `ParachainSystem::ValidationData` (r:1 w:0)
	/// Proof: `ParachainSystem::ValidationData` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn do_tick_base() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `408`
		//  Estimated: `1893`
		// Minimum execution time: 14_229_000 picoseconds.
		Weight::from_parts(15_177_000, 0)
			.saturating_add(Weight::from_parts(0, 1893))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::SaleInfo` (r:1 w:0)
	/// Proof: `Broker::SaleInfo` (`max_values`: Some(1), `max_size`: Some(57), added: 552, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Reservations` (r:1 w:1)
	/// Proof: `Broker::Reservations` (`max_values`: Some(1), `max_size`: Some(12021), added: 12516, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Workplan` (r:0 w:2)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	fn force_reserve() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `11141`
		//  Estimated: `13506`
		// Minimum execution time: 43_203_000 picoseconds.
		Weight::from_parts(45_670_000, 0)
			.saturating_add(Weight::from_parts(0, 13506))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Broker::Leases` (r:1 w:1)
	/// Proof: `Broker::Leases` (`max_values`: Some(1), `max_size`: Some(401), added: 896, mode: `MaxEncodedLen`)
	fn swap_leases() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `470`
		//  Estimated: `1886`
		// Minimum execution time: 7_773_000 picoseconds.
		Weight::from_parts(8_304_000, 0)
			.saturating_add(Weight::from_parts(0, 1886))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Broker::SaleInfo` (r:1 w:1)
	/// Proof: `Broker::SaleInfo` (`max_values`: Some(1), `max_size`: Some(57), added: 552, mode: `MaxEncodedLen`)
	/// Storage: `Broker::PotentialRenewals` (r:1 w:2)
	/// Proof: `Broker::PotentialRenewals` (`max_values`: None, `max_size`: Some(1233), added: 3708, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Configuration` (r:1 w:0)
	/// Proof: `Broker::Configuration` (`max_values`: Some(1), `max_size`: Some(31), added: 526, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Status` (r:1 w:0)
	/// Proof: `Broker::Status` (`max_values`: Some(1), `max_size`: Some(18), added: 513, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ParachainSystem::ValidationData` (r:1 w:0)
	/// Proof: `ParachainSystem::ValidationData` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Broker::AutoRenewals` (r:1 w:1)
	/// Proof: `Broker::AutoRenewals` (`max_values`: Some(1), `max_size`: Some(1002), added: 1497, mode: `MaxEncodedLen`)
	/// Storage: `Broker::Workplan` (r:0 w:1)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	fn enable_auto_renew() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `2829`
		//  Estimated: `6196`
		// Minimum execution time: 159_458_000 picoseconds.
		Weight::from_parts(174_911_000, 0)
			.saturating_add(Weight::from_parts(0, 6196))
			.saturating_add(T::DbWeight::get().reads(8))
			.saturating_add(T::DbWeight::get().writes(7))
	}
	/// Storage: `Broker::AutoRenewals` (r:1 w:1)
	/// Proof: `Broker::AutoRenewals` (`max_values`: Some(1), `max_size`: Some(1002), added: 1497, mode: `MaxEncodedLen`)
	fn disable_auto_renew() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1307`
		//  Estimated: `2487`
		// Minimum execution time: 31_994_000 picoseconds.
		Weight::from_parts(41_143_000, 0)
			.saturating_add(Weight::from_parts(0, 2487))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingUpwardMessages` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingUpwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn on_new_timeslice() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `261`
		//  Estimated: `3726`
		// Minimum execution time: 59_280_000 picoseconds.
		Weight::from_parts(62_361_000, 0)
			.saturating_add(Weight::from_parts(0, 3726))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Broker::Workplan` (r:1 w:1)
	/// Proof: `Broker::Workplan` (`max_values`: None, `max_size`: Some(1216), added: 3691, mode: `MaxEncodedLen`)
	fn remove_assignment() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `798`
		//  Estimated: `4681`
		// Minimum execution time: 23_100_000 picoseconds.
		Weight::from_parts(24_235_000, 0)
			.saturating_add(Weight::from_parts(0, 4681))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
