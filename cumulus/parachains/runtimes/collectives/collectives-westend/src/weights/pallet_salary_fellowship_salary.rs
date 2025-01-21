// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Cumulus.

// Cumulus is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Cumulus is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Cumulus.  If not, see <http://www.gnu.org/licenses/>.

//! Autogenerated weights for `pallet_salary`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `2ef552afe55a`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("collectives-westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=collectives-westend-dev
// --pallet=pallet_salary
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

/// Weight functions for `pallet_salary`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_salary::WeightInfo for WeightInfo<T> {
	/// Storage: `FellowshipSalary::Status` (r:1 w:1)
	/// Proof: `FellowshipSalary::Status` (`max_values`: Some(1), `max_size`: Some(56), added: 551, mode: `MaxEncodedLen`)
	fn init() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `142`
		//  Estimated: `1541`
		// Minimum execution time: 9_288_000 picoseconds.
		Weight::from_parts(9_685_000, 0)
			.saturating_add(Weight::from_parts(0, 1541))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `FellowshipSalary::Status` (r:1 w:1)
	/// Proof: `FellowshipSalary::Status` (`max_values`: Some(1), `max_size`: Some(56), added: 551, mode: `MaxEncodedLen`)
	fn bump() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `224`
		//  Estimated: `1541`
		// Minimum execution time: 11_010_000 picoseconds.
		Weight::from_parts(11_505_000, 0)
			.saturating_add(Weight::from_parts(0, 1541))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `FellowshipSalary::Status` (r:1 w:0)
	/// Proof: `FellowshipSalary::Status` (`max_values`: Some(1), `max_size`: Some(56), added: 551, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipCollective::Members` (r:1 w:0)
	/// Proof: `FellowshipCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipSalary::Claimant` (r:1 w:1)
	/// Proof: `FellowshipSalary::Claimant` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	fn induct() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `395`
		//  Estimated: `3551`
		// Minimum execution time: 19_545_000 picoseconds.
		Weight::from_parts(20_017_000, 0)
			.saturating_add(Weight::from_parts(0, 3551))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `FellowshipCollective::Members` (r:1 w:0)
	/// Proof: `FellowshipCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipSalary::Status` (r:1 w:1)
	/// Proof: `FellowshipSalary::Status` (`max_values`: Some(1), `max_size`: Some(56), added: 551, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipSalary::Claimant` (r:1 w:1)
	/// Proof: `FellowshipSalary::Claimant` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	fn register() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462`
		//  Estimated: `3551`
		// Minimum execution time: 23_048_000 picoseconds.
		Weight::from_parts(23_522_000, 0)
			.saturating_add(Weight::from_parts(0, 3551))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `FellowshipSalary::Status` (r:1 w:1)
	/// Proof: `FellowshipSalary::Status` (`max_values`: Some(1), `max_size`: Some(56), added: 551, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipSalary::Claimant` (r:1 w:1)
	/// Proof: `FellowshipSalary::Claimant` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipCollective::Members` (r:1 w:0)
	/// Proof: `FellowshipCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
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
		//  Measured:  `671`
		//  Estimated: `4136`
		// Minimum execution time: 66_621_000 picoseconds.
		Weight::from_parts(68_402_000, 0)
			.saturating_add(Weight::from_parts(0, 4136))
			.saturating_add(T::DbWeight::get().reads(9))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `FellowshipSalary::Status` (r:1 w:1)
	/// Proof: `FellowshipSalary::Status` (`max_values`: Some(1), `max_size`: Some(56), added: 551, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipSalary::Claimant` (r:1 w:1)
	/// Proof: `FellowshipSalary::Claimant` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipCollective::Members` (r:1 w:0)
	/// Proof: `FellowshipCollective::Members` (`max_values`: None, `max_size`: Some(42), added: 2517, mode: `MaxEncodedLen`)
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
	fn payout_other() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `671`
		//  Estimated: `4136`
		// Minimum execution time: 67_047_000 picoseconds.
		Weight::from_parts(68_744_000, 0)
			.saturating_add(Weight::from_parts(0, 4136))
			.saturating_add(T::DbWeight::get().reads(9))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `FellowshipSalary::Status` (r:1 w:1)
	/// Proof: `FellowshipSalary::Status` (`max_values`: Some(1), `max_size`: Some(56), added: 551, mode: `MaxEncodedLen`)
	/// Storage: `FellowshipSalary::Claimant` (r:1 w:1)
	/// Proof: `FellowshipSalary::Claimant` (`max_values`: None, `max_size`: Some(86), added: 2561, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::Queries` (r:1 w:1)
	/// Proof: `PolkadotXcm::Queries` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn check_payment() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `336`
		//  Estimated: `3801`
		// Minimum execution time: 27_430_000 picoseconds.
		Weight::from_parts(28_348_000, 0)
			.saturating_add(Weight::from_parts(0, 3801))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
	}
}
