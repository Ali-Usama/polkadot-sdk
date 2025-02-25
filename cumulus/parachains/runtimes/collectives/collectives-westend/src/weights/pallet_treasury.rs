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

//! Autogenerated weights for `pallet_treasury`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `d56afbdf93cb`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/collectives-westend-runtime/collectives_westend_runtime.wasm
// --pallet=pallet_treasury
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/collectives/collectives-westend/src/weights
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

/// Weight functions for `pallet_treasury`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_treasury::WeightInfo for WeightInfo<T> {
	/// Storage: `FellowshipTreasury::ProposalCount` (r:1 w:1)
	/// Proof: `FellowshipTreasury::ProposalCount` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipTreasury::Approvals` (r:1 w:1)
	/// Proof: `FellowshipTreasury::Approvals` (`max_values`: Some(1), `max_size`: Some(402), added: 897, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipTreasury::Proposals` (r:0 w:1)
	/// Proof: `FellowshipTreasury::Proposals` (`max_values`: None, `max_size`: Some(108), added: 2583, mode: `MaxEncodedLen`)
	fn spend_local() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76`
		//  Estimated: `1887`
		// Minimum execution time: 12_691_000 picoseconds.
		Weight::from_parts(13_305_000, 0)
			.saturating_add(Weight::from_parts(0, 1887))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `FellowshipTreasury::Approvals` (r:1 w:1)
	/// Proof: `FellowshipTreasury::Approvals` (`max_values`: Some(1), `max_size`: Some(402), added: 897, mode: `MaxEncodedLen`)
	fn remove_approval() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161`
		//  Estimated: `1887`
		// Minimum execution time: 7_127_000 picoseconds.
		Weight::from_parts(7_372_000, 0)
			.saturating_add(Weight::from_parts(0, 1887))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipTreasury::Deactivated` (r:1 w:1)
	/// Proof: `FellowshipTreasury::Deactivated` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipTreasury::LastSpendPeriod` (r:1 w:1)
	/// Proof: `FellowshipTreasury::LastSpendPeriod` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[0, 99]`.
	fn on_initialize_proposals(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `280 + p * (1 ±0)`
		//  Estimated: `3593`
		// Minimum execution time: 13_314_000 picoseconds.
		Weight::from_parts(17_273_814, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			// Standard Error: 1_387
			.saturating_add(Weight::from_parts(64_685, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `AssetRate::ConversionRateToNative` (r:1 w:0)
	/// Proof: `AssetRate::ConversionRateToNative` (`max_values`: None, `max_size`: Some(1238), added: 3713, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipTreasury::SpendCount` (r:1 w:1)
	/// Proof: `FellowshipTreasury::SpendCount` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipTreasury::Spends` (r:0 w:1)
	/// Proof: `FellowshipTreasury::Spends` (`max_values`: None, `max_size`: Some(1853), added: 4328, mode: `MaxEncodedLen`)
	fn spend() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `219`
		//  Estimated: `4703`
		// Minimum execution time: 23_634_000 picoseconds.
		Weight::from_parts(24_654_000, 0)
			.saturating_add(Weight::from_parts(0, 4703))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `FellowshipTreasury::Spends` (r:1 w:1)
	/// Proof: `FellowshipTreasury::Spends` (`max_values`: None, `max_size`: Some(1853), added: 4328, mode: `MaxEncodedLen`)
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::QueryCounter` (r:1 w:1)
	/// Proof: `PolkadotXcm::QueryCounter` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `XcmpQueue::DeliveryFeeFactor` (r:1 w:0)
	/// Proof: `XcmpQueue::DeliveryFeeFactor` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::RelevantMessagingState` (r:1 w:0)
	/// Proof: `ParachainSystem::RelevantMessagingState` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `XcmpQueue::OutboundXcmpStatus` (r:1 w:1)
	/// Proof: `XcmpQueue::OutboundXcmpStatus` (`max_values`: Some(1), `max_size`: Some(1282), added: 1777, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::OutboundXcmpMessages` (r:0 w:1)
	/// Proof: `XcmpQueue::OutboundXcmpMessages` (`max_values`: None, `max_size`: Some(105506), added: 107981, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::Queries` (r:0 w:1)
	/// Proof: `PolkadotXcm::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn payout() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `559`
		//  Estimated: `5318`
		// Minimum execution time: 58_903_000 picoseconds.
		Weight::from_parts(62_012_000, 0)
			.saturating_add(Weight::from_parts(0, 5318))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `FellowshipTreasury::Spends` (r:1 w:1)
	/// Proof: `FellowshipTreasury::Spends` (`max_values`: None, `max_size`: Some(1853), added: 4328, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::Queries` (r:1 w:1)
	/// Proof: `PolkadotXcm::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn check_status() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `240`
		//  Estimated: `5318`
		// Minimum execution time: 24_929_000 picoseconds.
		Weight::from_parts(25_859_000, 0)
			.saturating_add(Weight::from_parts(0, 5318))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `FellowshipTreasury::Spends` (r:1 w:1)
	/// Proof: `FellowshipTreasury::Spends` (`max_values`: None, `max_size`: Some(1853), added: 4328, mode: `MaxEncodedLen`)
	fn void_spend() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `212`
		//  Estimated: `5318`
		// Minimum execution time: 14_722_000 picoseconds.
		Weight::from_parts(15_398_000, 0)
			.saturating_add(Weight::from_parts(0, 5318))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
