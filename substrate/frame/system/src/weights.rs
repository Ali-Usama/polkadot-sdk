// This file is part of Substrate.

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

// This file is part of Substrate.

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

//! Autogenerated weights for `frame_system`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `4563561839a5`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: `1024`

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/kitchensink-runtime/kitchensink_runtime.wasm
// --pallet=frame_system
// --header=/__w/polkadot-sdk/polkadot-sdk/substrate/HEADER-APACHE2
// --output=/__w/polkadot-sdk/polkadot-sdk/substrate/frame/system/src/weights.rs
// --wasm-execution=compiled
// --steps=50
// --repeat=20
// --heap-pages=4096
// --template=substrate/.maintain/frame-weight-template.hbs
// --no-storage-info
// --no-min-squares
// --no-median-slopes
// --genesis-builder-policy=none
// --exclude-pallets=pallet_xcm,pallet_xcm_benchmarks::fungible,pallet_xcm_benchmarks::generic,pallet_nomination_pools,pallet_remark,pallet_transaction_storage,pallet_election_provider_multi_block,pallet_election_provider_multi_block::signed,pallet_election_provider_multi_block::unsigned,pallet_election_provider_multi_block::verifier

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]
#![allow(dead_code)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for `frame_system`.
pub trait WeightInfo {
	fn remark(b: u32, ) -> Weight;
	fn remark_with_event(b: u32, ) -> Weight;
	fn set_heap_pages() -> Weight;
	fn set_code() -> Weight;
	fn set_storage(i: u32, ) -> Weight;
	fn kill_storage(i: u32, ) -> Weight;
	fn kill_prefix(p: u32, ) -> Weight;
	fn authorize_upgrade() -> Weight;
	fn apply_authorized_upgrade() -> Weight;
}

/// Weights for `frame_system` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: crate::Config> WeightInfo for SubstrateWeight<T> {
	/// The range of component `b` is `[0, 3932160]`.
	fn remark(b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 1_518_000 picoseconds.
		Weight::from_parts(1_586_000, 0)
			// Standard Error: 122
			.saturating_add(Weight::from_parts(10_920, 0).saturating_mul(b.into()))
	}
	/// The range of component `b` is `[0, 3932160]`.
	fn remark_with_event(b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 4_558_000 picoseconds.
		Weight::from_parts(4_725_000, 0)
			// Standard Error: 120
			.saturating_add(Weight::from_parts(12_386, 0).saturating_mul(b.into()))
	}
	/// Storage: UNKNOWN KEY `0x3a686561707061676573` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a686561707061676573` (r:0 w:1)
	fn set_heap_pages() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_639_000 picoseconds.
		Weight::from_parts(2_836_000, 0)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `MultiBlockMigrations::Cursor` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	fn set_code() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `67035`
		// Minimum execution time: 161_314_402_000 picoseconds.
		Weight::from_parts(164_247_810_000, 67035)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `i` is `[0, 1000]`.
	fn set_storage(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 1_518_000 picoseconds.
		Weight::from_parts(1_565_000, 0)
			// Standard Error: 2_255
			.saturating_add(Weight::from_parts(733_648, 0).saturating_mul(i.into()))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(i.into())))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `i` is `[0, 1000]`.
	fn kill_storage(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 1_583_000 picoseconds.
		Weight::from_parts(1_624_000, 0)
			// Standard Error: 1_360
			.saturating_add(Weight::from_parts(566_903, 0).saturating_mul(i.into()))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(i.into())))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `p` is `[0, 1000]`.
	fn kill_prefix(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `12 + p * (69 ±0)`
		//  Estimated: `0 + p * (70 ±0)`
		// Minimum execution time: 2_884_000 picoseconds.
		Weight::from_parts(2_964_000, 0)
			// Standard Error: 1_896
			.saturating_add(Weight::from_parts(1_340_742, 0).saturating_mul(p.into()))
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
		// Minimum execution time: 12_466_000 picoseconds.
		Weight::from_parts(15_570_000, 0)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `System::AuthorizedUpgrade` (r:1 w:1)
	/// Proof: `System::AuthorizedUpgrade` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockMigrations::Cursor` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	fn apply_authorized_upgrade() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `21`
		//  Estimated: `67035`
		// Minimum execution time: 163_673_542_000 picoseconds.
		Weight::from_parts(166_858_158_000, 67035)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// The range of component `b` is `[0, 3932160]`.
	fn remark(b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 1_518_000 picoseconds.
		Weight::from_parts(1_586_000, 0)
			// Standard Error: 122
			.saturating_add(Weight::from_parts(10_920, 0).saturating_mul(b.into()))
	}
	/// The range of component `b` is `[0, 3932160]`.
	fn remark_with_event(b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 4_558_000 picoseconds.
		Weight::from_parts(4_725_000, 0)
			// Standard Error: 120
			.saturating_add(Weight::from_parts(12_386, 0).saturating_mul(b.into()))
	}
	/// Storage: UNKNOWN KEY `0x3a686561707061676573` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a686561707061676573` (r:0 w:1)
	fn set_heap_pages() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_639_000 picoseconds.
		Weight::from_parts(2_836_000, 0)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `MultiBlockMigrations::Cursor` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	fn set_code() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `67035`
		// Minimum execution time: 161_314_402_000 picoseconds.
		Weight::from_parts(164_247_810_000, 67035)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `i` is `[0, 1000]`.
	fn set_storage(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 1_518_000 picoseconds.
		Weight::from_parts(1_565_000, 0)
			// Standard Error: 2_255
			.saturating_add(Weight::from_parts(733_648, 0).saturating_mul(i.into()))
			.saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(i.into())))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `i` is `[0, 1000]`.
	fn kill_storage(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 1_583_000 picoseconds.
		Weight::from_parts(1_624_000, 0)
			// Standard Error: 1_360
			.saturating_add(Weight::from_parts(566_903, 0).saturating_mul(i.into()))
			.saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(i.into())))
	}
	/// Storage: `Skipped::Metadata` (r:0 w:0)
	/// Proof: `Skipped::Metadata` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `p` is `[0, 1000]`.
	fn kill_prefix(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `12 + p * (69 ±0)`
		//  Estimated: `0 + p * (70 ±0)`
		// Minimum execution time: 2_884_000 picoseconds.
		Weight::from_parts(2_964_000, 0)
			// Standard Error: 1_896
			.saturating_add(Weight::from_parts(1_340_742, 0).saturating_mul(p.into()))
			.saturating_add(RocksDbWeight::get().reads((1_u64).saturating_mul(p.into())))
			.saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(p.into())))
			.saturating_add(Weight::from_parts(0, 70).saturating_mul(p.into()))
	}
	/// Storage: `System::AuthorizedUpgrade` (r:0 w:1)
	/// Proof: `System::AuthorizedUpgrade` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	fn authorize_upgrade() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 12_466_000 picoseconds.
		Weight::from_parts(15_570_000, 0)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `System::AuthorizedUpgrade` (r:1 w:1)
	/// Proof: `System::AuthorizedUpgrade` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `MultiBlockMigrations::Cursor` (r:1 w:0)
	/// Proof: `MultiBlockMigrations::Cursor` (`max_values`: Some(1), `max_size`: Some(65550), added: 66045, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a636f6465` (r:0 w:1)
	fn apply_authorized_upgrade() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `21`
		//  Estimated: `67035`
		// Minimum execution time: 163_673_542_000 picoseconds.
		Weight::from_parts(166_858_158_000, 67035)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
}
