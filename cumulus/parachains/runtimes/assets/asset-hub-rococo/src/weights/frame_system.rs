// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Cumulus.
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

//! Autogenerated weights for `frame_system`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-07-31, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-ynta1nyy-project-238-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! EXECUTION: ``, WASM-EXECUTION: `Compiled`, CHAIN: `Some("asset-hub-rococo-dev")`, DB CACHE: 1024

// Executed Command:
// ./target/production/polkadot-parachain
// benchmark
// pallet
// --chain=asset-hub-rococo-dev
// --wasm-execution=compiled
// --pallet=frame_system
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --extrinsic=*
// --steps=50
// --repeat=20
// --json
// --header=./file_header.txt
// --output=./parachains/runtimes/assets/asset-hub-rococo/src/weights/

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::Weight};
use core::marker::PhantomData;

/// Weight functions for `frame_system`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> frame_system::WeightInfo for WeightInfo<T> {
	/// The range of component `b` is `[0, 3932160]`.
	fn remark(b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_106_000 picoseconds.
		Weight::from_parts(1_884_213, 0)
			.saturating_add(Weight::from_parts(0, 0))
			// Standard Error: 0
			.saturating_add(Weight::from_parts(388, 0).saturating_mul(b.into()))
	}
	/// The range of component `b` is `[0, 3932160]`.
	fn remark_with_event(b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 7_528_000 picoseconds.
		Weight::from_parts(27_081_927, 0)
			.saturating_add(Weight::from_parts(0, 0))
			// Standard Error: 7
			.saturating_add(Weight::from_parts(1_730, 0).saturating_mul(b.into()))
	}
	/// Storage: `System::Digest` (r:1 w:1)
	/// Proof: `System::Digest` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: UNKNOWN KEY `0x3a686561707061676573` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a686561707061676573` (r:0 w:1)
	fn set_heap_pages() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `1485`
		// Minimum execution time: 3_882_000 picoseconds.
		Weight::from_parts(4_149_000, 0)
			.saturating_add(Weight::from_parts(0, 1485))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `ParachainSystem::ValidationData` (r:1 w:0)
	/// Proof: `ParachainSystem::ValidationData` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::UpgradeRestrictionSignal` (r:1 w:0)
	/// Proof: `ParachainSystem::UpgradeRestrictionSignal` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::PendingValidationCode` (r:1 w:1)
	/// Proof: `ParachainSystem::PendingValidationCode` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::HostConfiguration` (r:1 w:0)
	/// Proof: `ParachainSystem::HostConfiguration` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::NewValidationCode` (r:0 w:1)
	/// Proof: `ParachainSystem::NewValidationCode` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::DidSetValidationCode` (r:0 w:1)
	/// Proof: `ParachainSystem::DidSetValidationCode` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn set_code() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `119`
		//  Estimated: `1604`
		// Minimum execution time: 103_389_161_000 picoseconds.
		Weight::from_parts(106_870_091_000, 0)
			.saturating_add(Weight::from_parts(0, 1604))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `i` is `[0, 1000]`.
	fn set_storage(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_236_000 picoseconds.
		Weight::from_parts(2_302_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			// Standard Error: 2_045
			.saturating_add(Weight::from_parts(763_456, 0).saturating_mul(i.into()))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(i.into())))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `i` is `[0, 1000]`.
	fn kill_storage(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_175_000 picoseconds.
		Weight::from_parts(2_238_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			// Standard Error: 1_040
			.saturating_add(Weight::from_parts(571_397, 0).saturating_mul(i.into()))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(i.into())))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `p` is `[0, 1000]`.
	fn kill_prefix(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `84 + p * (69 ±0)`
		//  Estimated: `80 + p * (70 ±0)`
		// Minimum execution time: 3_843_000 picoseconds.
		Weight::from_parts(3_947_000, 0)
			.saturating_add(Weight::from_parts(0, 80))
			// Standard Error: 2_188
			.saturating_add(Weight::from_parts(1_212_360, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(p.into())))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(p.into())))
			.saturating_add(Weight::from_parts(0, 70).saturating_mul(p.into()))
	}
	/// Storage: `System::AuthorizedUpgrade` (r:0 w:1)
	/// Proof: `System::AuthorizedUpgrade` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	fn authorize_upgrade() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 33_027_000 picoseconds.
		Weight::from_parts(33_027_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `System::AuthorizedUpgrade` (r:1 w:1)
	/// Proof: `System::AuthorizedUpgrade` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `System::Digest` (r:1 w:1)
	/// Proof: `System::Digest` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	fn apply_authorized_upgrade() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `22`
		//  Estimated: `1518`
		// Minimum execution time: 118_101_992_000 picoseconds.
		Weight::from_parts(118_101_992_000, 0)
			.saturating_add(Weight::from_parts(0, 1518))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	fn validate_apply_authorized_upgrade() -> Weight {
		Weight::zero()
	}
}
