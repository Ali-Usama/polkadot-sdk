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

//! Autogenerated weights for `pallet_membership`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-17, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `265dfb6aaaa9`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("dev")`, DB CACHE: `1024`

// Executed Command:
// target/production/substrate-node
// benchmark
// pallet
// --extrinsic=*
// --chain=dev
// --pallet=pallet_membership
// --header=/__w/polkadot-sdk/polkadot-sdk/substrate/HEADER-APACHE2
// --output=/__w/polkadot-sdk/polkadot-sdk/substrate/frame/membership/src/weights.rs
// --wasm-execution=compiled
// --steps=50
// --repeat=20
// --heap-pages=4096
// --template=substrate/.maintain/frame-weight-template.hbs
// --no-storage-info
// --no-min-squares
// --no-median-slopes

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for `pallet_membership`.
pub trait WeightInfo {
	fn add_member(m: u32, ) -> Weight;
	fn remove_member(m: u32, ) -> Weight;
	fn swap_member(m: u32, ) -> Weight;
	fn reset_members(m: u32, ) -> Weight;
	fn change_key(m: u32, ) -> Weight;
	fn set_prime(m: u32, ) -> Weight;
	fn clear_prime() -> Weight;
}

/// Weights for `pallet_membership` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[1, 99]`.
	fn add_member(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `207 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 17_963_000 picoseconds.
		Weight::from_parts(19_041_715, 4687)
			// Standard Error: 854
			.saturating_add(Weight::from_parts(26_872, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalMembership::Prime` (r:1 w:0)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[2, 100]`.
	fn remove_member(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `311 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 20_879_000 picoseconds.
		Weight::from_parts(21_967_691, 4687)
			// Standard Error: 704
			.saturating_add(Weight::from_parts(18_057, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalMembership::Prime` (r:1 w:0)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[2, 100]`.
	fn swap_member(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `311 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 21_113_000 picoseconds.
		Weight::from_parts(21_899_372, 4687)
			// Standard Error: 786
			.saturating_add(Weight::from_parts(42_428, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalMembership::Prime` (r:1 w:0)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[1, 100]`.
	fn reset_members(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `311 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 20_568_000 picoseconds.
		Weight::from_parts(22_113_232, 4687)
			// Standard Error: 815
			.saturating_add(Weight::from_parts(131_612, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalMembership::Prime` (r:1 w:1)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[1, 100]`.
	fn change_key(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `311 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 21_316_000 picoseconds.
		Weight::from_parts(22_250_591, 4687)
			// Standard Error: 1_269
			.saturating_add(Weight::from_parts(44_428, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(4_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:0)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalMembership::Prime` (r:0 w:1)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[1, 100]`.
	fn set_prime(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `31 + m * (32 ±0)`
		//  Estimated: `4687 + m * (32 ±0)`
		// Minimum execution time: 6_826_000 picoseconds.
		Weight::from_parts(7_452_831, 4687)
			// Standard Error: 221
			.saturating_add(Weight::from_parts(8_533, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_parts(0, 32).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Prime` (r:0 w:1)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn clear_prime() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_465_000 picoseconds.
		Weight::from_parts(2_610_000, 0)
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[1, 99]`.
	fn add_member(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `207 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 17_963_000 picoseconds.
		Weight::from_parts(19_041_715, 4687)
			// Standard Error: 854
			.saturating_add(Weight::from_parts(26_872, 0).saturating_mul(m.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalMembership::Prime` (r:1 w:0)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[2, 100]`.
	fn remove_member(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `311 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 20_879_000 picoseconds.
		Weight::from_parts(21_967_691, 4687)
			// Standard Error: 704
			.saturating_add(Weight::from_parts(18_057, 0).saturating_mul(m.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalMembership::Prime` (r:1 w:0)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[2, 100]`.
	fn swap_member(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `311 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 21_113_000 picoseconds.
		Weight::from_parts(21_899_372, 4687)
			// Standard Error: 786
			.saturating_add(Weight::from_parts(42_428, 0).saturating_mul(m.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalMembership::Prime` (r:1 w:0)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[1, 100]`.
	fn reset_members(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `311 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 20_568_000 picoseconds.
		Weight::from_parts(22_113_232, 4687)
			// Standard Error: 815
			.saturating_add(Weight::from_parts(131_612, 0).saturating_mul(m.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:1)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Proposals` (r:1 w:0)
	/// Proof: `TechnicalCommittee::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalMembership::Prime` (r:1 w:1)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Members` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[1, 100]`.
	fn change_key(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `311 + m * (64 ±0)`
		//  Estimated: `4687 + m * (64 ±0)`
		// Minimum execution time: 21_316_000 picoseconds.
		Weight::from_parts(22_250_591, 4687)
			// Standard Error: 1_269
			.saturating_add(Weight::from_parts(44_428, 0).saturating_mul(m.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Members` (r:1 w:0)
	/// Proof: `TechnicalMembership::Members` (`max_values`: Some(1), `max_size`: Some(3202), added: 3697, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalMembership::Prime` (r:0 w:1)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[1, 100]`.
	fn set_prime(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `31 + m * (32 ±0)`
		//  Estimated: `4687 + m * (32 ±0)`
		// Minimum execution time: 6_826_000 picoseconds.
		Weight::from_parts(7_452_831, 4687)
			// Standard Error: 221
			.saturating_add(Weight::from_parts(8_533, 0).saturating_mul(m.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_parts(0, 32).saturating_mul(m.into()))
	}
	/// Storage: `TechnicalMembership::Prime` (r:0 w:1)
	/// Proof: `TechnicalMembership::Prime` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `TechnicalCommittee::Prime` (r:0 w:1)
	/// Proof: `TechnicalCommittee::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn clear_prime() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_465_000 picoseconds.
		Weight::from_parts(2_610_000, 0)
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
}
