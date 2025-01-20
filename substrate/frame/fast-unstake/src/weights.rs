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

//! Autogenerated weights for `pallet_fast_unstake`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-20, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `4f38abe89714`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("dev")`, DB CACHE: `1024`

// Executed Command:
// target/production/substrate-node
// benchmark
// pallet
// --extrinsic=*
// --chain=dev
// --pallet=pallet_fast_unstake
// --header=/__w/polkadot-sdk/polkadot-sdk/substrate/HEADER-APACHE2
// --output=/__w/polkadot-sdk/polkadot-sdk/substrate/frame/fast-unstake/src/weights.rs
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

/// Weight functions needed for `pallet_fast_unstake`.
pub trait WeightInfo {
	fn on_idle_unstake(b: u32, ) -> Weight;
	fn on_idle_check(v: u32, b: u32, ) -> Weight;
	fn register_fast_unstake() -> Weight;
	fn deregister() -> Weight;
	fn control() -> Weight;
}

/// Weights for `pallet_fast_unstake` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:1 w:0)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ValidatorCount` (r:1 w:0)
	/// Proof: `Staking::ValidatorCount` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Head` (r:1 w:1)
	/// Proof: `FastUnstake::Head` (`max_values`: Some(1), `max_size`: Some(5768), added: 6263, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::CounterForQueue` (r:1 w:0)
	/// Proof: `FastUnstake::CounterForQueue` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `ElectionProviderMultiPhase::CurrentPhase` (r:1 w:0)
	/// Proof: `ElectionProviderMultiPhase::CurrentPhase` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::CurrentEra` (r:1 w:0)
	/// Proof: `Staking::CurrentEra` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::SlashingSpans` (r:64 w:0)
	/// Proof: `Staking::SlashingSpans` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::Bonded` (r:64 w:64)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Ledger` (r:64 w:64)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `MaxEncodedLen`)
	/// Storage: `Staking::VirtualStakers` (r:64 w:64)
	/// Proof: `Staking::VirtualStakers` (`max_values`: None, `max_size`: Some(40), added: 2515, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:64 w:64)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(409), added: 2884, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:64 w:64)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Validators` (r:64 w:0)
	/// Proof: `Staking::Validators` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Nominators` (r:64 w:0)
	/// Proof: `Staking::Nominators` (`max_values`: None, `max_size`: Some(558), added: 3033, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Payee` (r:0 w:64)
	/// Proof: `Staking::Payee` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// The range of component `b` is `[1, 64]`.
	fn on_idle_unstake(b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1608 + b * (445 ±0)`
		//  Estimated: `7253 + b * (3566 ±0)`
		// Minimum execution time: 112_898_000 picoseconds.
		Weight::from_parts(51_128_988, 7253)
			// Standard Error: 38_058
			.saturating_add(Weight::from_parts(73_782_072, 0).saturating_mul(b.into()))
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().reads((8_u64).saturating_mul(b.into())))
			.saturating_add(T::DbWeight::get().writes(1_u64))
			.saturating_add(T::DbWeight::get().writes((6_u64).saturating_mul(b.into())))
			.saturating_add(Weight::from_parts(0, 3566).saturating_mul(b.into()))
	}
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:1 w:0)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ValidatorCount` (r:1 w:0)
	/// Proof: `Staking::ValidatorCount` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Head` (r:1 w:1)
	/// Proof: `FastUnstake::Head` (`max_values`: Some(1), `max_size`: Some(5768), added: 6263, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::CounterForQueue` (r:1 w:0)
	/// Proof: `FastUnstake::CounterForQueue` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `ElectionProviderMultiPhase::CurrentPhase` (r:1 w:0)
	/// Proof: `ElectionProviderMultiPhase::CurrentPhase` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::CurrentEra` (r:1 w:0)
	/// Proof: `Staking::CurrentEra` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStakers` (r:1 w:0)
	/// Proof: `Staking::ErasStakers` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ErasStakersPaged` (r:257 w:0)
	/// Proof: `Staking::ErasStakersPaged` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `v` is `[1, 256]`.
	/// The range of component `b` is `[1, 64]`.
	fn on_idle_check(v: u32, b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1945 + b * (55 ±0) + v * (10055 ±0)`
		//  Estimated: `7253 + b * (56 ±0) + v * (12531 ±0)`
		// Minimum execution time: 1_873_520_000 picoseconds.
		Weight::from_parts(1_883_310_000, 7253)
			// Standard Error: 13_420_326
			.saturating_add(Weight::from_parts(430_621_598, 0).saturating_mul(v.into()))
			// Standard Error: 53_696_253
			.saturating_add(Weight::from_parts(1_687_132_368, 0).saturating_mul(b.into()))
			.saturating_add(T::DbWeight::get().reads(8_u64))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(v.into())))
			.saturating_add(T::DbWeight::get().writes(1_u64))
			.saturating_add(Weight::from_parts(0, 56).saturating_mul(b.into()))
			.saturating_add(Weight::from_parts(0, 12531).saturating_mul(v.into()))
	}
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:1 w:0)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Ledger` (r:1 w:1)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Bonded` (r:1 w:0)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Queue` (r:1 w:1)
	/// Proof: `FastUnstake::Queue` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Head` (r:1 w:0)
	/// Proof: `FastUnstake::Head` (`max_values`: Some(1), `max_size`: Some(5768), added: 6263, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Validators` (r:1 w:0)
	/// Proof: `Staking::Validators` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Nominators` (r:1 w:1)
	/// Proof: `Staking::Nominators` (`max_values`: None, `max_size`: Some(558), added: 3033, mode: `MaxEncodedLen`)
	/// Storage: `Staking::CounterForNominators` (r:1 w:1)
	/// Proof: `Staking::CounterForNominators` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `VoterList::ListNodes` (r:1 w:1)
	/// Proof: `VoterList::ListNodes` (`max_values`: None, `max_size`: Some(154), added: 2629, mode: `MaxEncodedLen`)
	/// Storage: `VoterList::ListBags` (r:1 w:1)
	/// Proof: `VoterList::ListBags` (`max_values`: None, `max_size`: Some(82), added: 2557, mode: `MaxEncodedLen`)
	/// Storage: `VoterList::CounterForListNodes` (r:1 w:1)
	/// Proof: `VoterList::CounterForListNodes` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::CurrentEra` (r:1 w:0)
	/// Proof: `Staking::CurrentEra` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::VirtualStakers` (r:1 w:0)
	/// Proof: `Staking::VirtualStakers` (`max_values`: None, `max_size`: Some(40), added: 2515, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:0)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(409), added: 2884, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::CounterForQueue` (r:1 w:1)
	/// Proof: `FastUnstake::CounterForQueue` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn register_fast_unstake() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `2046`
		//  Estimated: `7253`
		// Minimum execution time: 145_318_000 picoseconds.
		Weight::from_parts(150_248_000, 7253)
			.saturating_add(T::DbWeight::get().reads(15_u64))
			.saturating_add(T::DbWeight::get().writes(8_u64))
	}
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:1 w:0)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Ledger` (r:1 w:0)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Bonded` (r:1 w:0)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Queue` (r:1 w:1)
	/// Proof: `FastUnstake::Queue` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Head` (r:1 w:0)
	/// Proof: `FastUnstake::Head` (`max_values`: Some(1), `max_size`: Some(5768), added: 6263, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::CounterForQueue` (r:1 w:1)
	/// Proof: `FastUnstake::CounterForQueue` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn deregister() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1416`
		//  Estimated: `7253`
		// Minimum execution time: 56_288_000 picoseconds.
		Weight::from_parts(58_035_000, 7253)
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:0 w:1)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn control() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_202_000 picoseconds.
		Weight::from_parts(2_309_000, 0)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:1 w:0)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ValidatorCount` (r:1 w:0)
	/// Proof: `Staking::ValidatorCount` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Head` (r:1 w:1)
	/// Proof: `FastUnstake::Head` (`max_values`: Some(1), `max_size`: Some(5768), added: 6263, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::CounterForQueue` (r:1 w:0)
	/// Proof: `FastUnstake::CounterForQueue` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `ElectionProviderMultiPhase::CurrentPhase` (r:1 w:0)
	/// Proof: `ElectionProviderMultiPhase::CurrentPhase` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::CurrentEra` (r:1 w:0)
	/// Proof: `Staking::CurrentEra` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::SlashingSpans` (r:64 w:0)
	/// Proof: `Staking::SlashingSpans` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::Bonded` (r:64 w:64)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Ledger` (r:64 w:64)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `MaxEncodedLen`)
	/// Storage: `Staking::VirtualStakers` (r:64 w:64)
	/// Proof: `Staking::VirtualStakers` (`max_values`: None, `max_size`: Some(40), added: 2515, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:64 w:64)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(409), added: 2884, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:64 w:64)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Validators` (r:64 w:0)
	/// Proof: `Staking::Validators` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Nominators` (r:64 w:0)
	/// Proof: `Staking::Nominators` (`max_values`: None, `max_size`: Some(558), added: 3033, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Payee` (r:0 w:64)
	/// Proof: `Staking::Payee` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// The range of component `b` is `[1, 64]`.
	fn on_idle_unstake(b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1608 + b * (445 ±0)`
		//  Estimated: `7253 + b * (3566 ±0)`
		// Minimum execution time: 112_898_000 picoseconds.
		Weight::from_parts(51_128_988, 7253)
			// Standard Error: 38_058
			.saturating_add(Weight::from_parts(73_782_072, 0).saturating_mul(b.into()))
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().reads((8_u64).saturating_mul(b.into())))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
			.saturating_add(RocksDbWeight::get().writes((6_u64).saturating_mul(b.into())))
			.saturating_add(Weight::from_parts(0, 3566).saturating_mul(b.into()))
	}
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:1 w:0)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ValidatorCount` (r:1 w:0)
	/// Proof: `Staking::ValidatorCount` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Head` (r:1 w:1)
	/// Proof: `FastUnstake::Head` (`max_values`: Some(1), `max_size`: Some(5768), added: 6263, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::CounterForQueue` (r:1 w:0)
	/// Proof: `FastUnstake::CounterForQueue` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `ElectionProviderMultiPhase::CurrentPhase` (r:1 w:0)
	/// Proof: `ElectionProviderMultiPhase::CurrentPhase` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::CurrentEra` (r:1 w:0)
	/// Proof: `Staking::CurrentEra` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStakers` (r:1 w:0)
	/// Proof: `Staking::ErasStakers` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ErasStakersPaged` (r:257 w:0)
	/// Proof: `Staking::ErasStakersPaged` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `v` is `[1, 256]`.
	/// The range of component `b` is `[1, 64]`.
	fn on_idle_check(v: u32, b: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1945 + b * (55 ±0) + v * (10055 ±0)`
		//  Estimated: `7253 + b * (56 ±0) + v * (12531 ±0)`
		// Minimum execution time: 1_873_520_000 picoseconds.
		Weight::from_parts(1_883_310_000, 7253)
			// Standard Error: 13_420_326
			.saturating_add(Weight::from_parts(430_621_598, 0).saturating_mul(v.into()))
			// Standard Error: 53_696_253
			.saturating_add(Weight::from_parts(1_687_132_368, 0).saturating_mul(b.into()))
			.saturating_add(RocksDbWeight::get().reads(8_u64))
			.saturating_add(RocksDbWeight::get().reads((1_u64).saturating_mul(v.into())))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
			.saturating_add(Weight::from_parts(0, 56).saturating_mul(b.into()))
			.saturating_add(Weight::from_parts(0, 12531).saturating_mul(v.into()))
	}
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:1 w:0)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Ledger` (r:1 w:1)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Bonded` (r:1 w:0)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Queue` (r:1 w:1)
	/// Proof: `FastUnstake::Queue` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Head` (r:1 w:0)
	/// Proof: `FastUnstake::Head` (`max_values`: Some(1), `max_size`: Some(5768), added: 6263, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Validators` (r:1 w:0)
	/// Proof: `Staking::Validators` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Nominators` (r:1 w:1)
	/// Proof: `Staking::Nominators` (`max_values`: None, `max_size`: Some(558), added: 3033, mode: `MaxEncodedLen`)
	/// Storage: `Staking::CounterForNominators` (r:1 w:1)
	/// Proof: `Staking::CounterForNominators` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `VoterList::ListNodes` (r:1 w:1)
	/// Proof: `VoterList::ListNodes` (`max_values`: None, `max_size`: Some(154), added: 2629, mode: `MaxEncodedLen`)
	/// Storage: `VoterList::ListBags` (r:1 w:1)
	/// Proof: `VoterList::ListBags` (`max_values`: None, `max_size`: Some(82), added: 2557, mode: `MaxEncodedLen`)
	/// Storage: `VoterList::CounterForListNodes` (r:1 w:1)
	/// Proof: `VoterList::CounterForListNodes` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::CurrentEra` (r:1 w:0)
	/// Proof: `Staking::CurrentEra` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::VirtualStakers` (r:1 w:0)
	/// Proof: `Staking::VirtualStakers` (`max_values`: None, `max_size`: Some(40), added: 2515, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Holds` (r:1 w:0)
	/// Proof: `Balances::Holds` (`max_values`: None, `max_size`: Some(409), added: 2884, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::CounterForQueue` (r:1 w:1)
	/// Proof: `FastUnstake::CounterForQueue` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn register_fast_unstake() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `2046`
		//  Estimated: `7253`
		// Minimum execution time: 145_318_000 picoseconds.
		Weight::from_parts(150_248_000, 7253)
			.saturating_add(RocksDbWeight::get().reads(15_u64))
			.saturating_add(RocksDbWeight::get().writes(8_u64))
	}
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:1 w:0)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Ledger` (r:1 w:0)
	/// Proof: `Staking::Ledger` (`max_values`: None, `max_size`: Some(1091), added: 3566, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Bonded` (r:1 w:0)
	/// Proof: `Staking::Bonded` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Queue` (r:1 w:1)
	/// Proof: `FastUnstake::Queue` (`max_values`: None, `max_size`: Some(56), added: 2531, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::Head` (r:1 w:0)
	/// Proof: `FastUnstake::Head` (`max_values`: Some(1), `max_size`: Some(5768), added: 6263, mode: `MaxEncodedLen`)
	/// Storage: `FastUnstake::CounterForQueue` (r:1 w:1)
	/// Proof: `FastUnstake::CounterForQueue` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn deregister() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1416`
		//  Estimated: `7253`
		// Minimum execution time: 56_288_000 picoseconds.
		Weight::from_parts(58_035_000, 7253)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: `FastUnstake::ErasToCheckPerBlock` (r:0 w:1)
	/// Proof: `FastUnstake::ErasToCheckPerBlock` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn control() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_202_000 picoseconds.
		Weight::from_parts(2_309_000, 0)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
}
