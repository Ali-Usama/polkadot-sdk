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

//! Autogenerated weights for `pallet_offences`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `802a4f773b26`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: `1024`

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/kitchensink-runtime/kitchensink_runtime.wasm
// --pallet=pallet_offences
// --header=/__w/polkadot-sdk/polkadot-sdk/substrate/HEADER-APACHE2
// --output=/__w/polkadot-sdk/polkadot-sdk/substrate/frame/offences/src/weights.rs
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

/// Weight functions needed for `pallet_offences`.
pub trait WeightInfo {
	fn report_offence_grandpa(n: u32, ) -> Weight;
	fn report_offence_babe(n: u32, ) -> Weight;
}

/// Weights for `pallet_offences` using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `Offences::ConcurrentReportsIndex` (r:1 w:1)
	/// Proof: `Offences::ConcurrentReportsIndex` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Offences::Reports` (r:1 w:1)
	/// Proof: `Offences::Reports` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ActiveEra` (r:1 w:0)
	/// Proof: `Staking::ActiveEra` (`max_values`: Some(1), `max_size`: Some(13), added: 508, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStartSessionIndex` (r:1 w:0)
	/// Proof: `Staking::ErasStartSessionIndex` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Invulnerables` (r:1 w:0)
	/// Proof: `Staking::Invulnerables` (`max_values`: Some(1), `max_size`: Some(641), added: 1136, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStakersOverview` (r:1 w:0)
	/// Proof: `Staking::ErasStakersOverview` (`max_values`: None, `max_size`: Some(92), added: 2567, mode: `MaxEncodedLen`)
	/// Storage: `Session::DisabledValidators` (r:1 w:1)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::Validators` (r:1 w:0)
	/// Proof: `Session::Validators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ValidatorSlashInEra` (r:1 w:1)
	/// Proof: `Staking::ValidatorSlashInEra` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `Staking::OffenceQueue` (r:1 w:1)
	/// Proof: `Staking::OffenceQueue` (`max_values`: None, `max_size`: Some(101), added: 2576, mode: `MaxEncodedLen`)
	/// Storage: `Staking::OffenceQueueEras` (r:1 w:1)
	/// Proof: `Staking::OffenceQueueEras` (`max_values`: Some(1), `max_size`: Some(2690), added: 3185, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 16]`.
	fn report_offence_grandpa(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `424`
		//  Estimated: `4175 + n * (1 ±0)`
		// Minimum execution time: 39_700_000 picoseconds.
		Weight::from_parts(41_685_972, 4175)
			// Standard Error: 5_328
			.saturating_add(Weight::from_parts(449_149, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(11_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
			.saturating_add(Weight::from_parts(0, 1).saturating_mul(n.into()))
	}
	/// Storage: `Offences::ConcurrentReportsIndex` (r:1 w:1)
	/// Proof: `Offences::ConcurrentReportsIndex` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Offences::Reports` (r:1 w:1)
	/// Proof: `Offences::Reports` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ActiveEra` (r:1 w:0)
	/// Proof: `Staking::ActiveEra` (`max_values`: Some(1), `max_size`: Some(13), added: 508, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStartSessionIndex` (r:1 w:0)
	/// Proof: `Staking::ErasStartSessionIndex` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Invulnerables` (r:1 w:0)
	/// Proof: `Staking::Invulnerables` (`max_values`: Some(1), `max_size`: Some(641), added: 1136, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStakersOverview` (r:1 w:0)
	/// Proof: `Staking::ErasStakersOverview` (`max_values`: None, `max_size`: Some(92), added: 2567, mode: `MaxEncodedLen`)
	/// Storage: `Session::DisabledValidators` (r:1 w:1)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::Validators` (r:1 w:0)
	/// Proof: `Session::Validators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ValidatorSlashInEra` (r:1 w:1)
	/// Proof: `Staking::ValidatorSlashInEra` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `Staking::OffenceQueue` (r:1 w:1)
	/// Proof: `Staking::OffenceQueue` (`max_values`: None, `max_size`: Some(101), added: 2576, mode: `MaxEncodedLen`)
	/// Storage: `Staking::OffenceQueueEras` (r:1 w:1)
	/// Proof: `Staking::OffenceQueueEras` (`max_values`: Some(1), `max_size`: Some(2690), added: 3185, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 16]`.
	fn report_offence_babe(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `424`
		//  Estimated: `4175 + n * (1 ±0)`
		// Minimum execution time: 39_468_000 picoseconds.
		Weight::from_parts(41_735_370, 4175)
			// Standard Error: 5_463
			.saturating_add(Weight::from_parts(397_177, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(11_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
			.saturating_add(Weight::from_parts(0, 1).saturating_mul(n.into()))
	}
}

// For backwards compatibility and tests.
impl WeightInfo for () {
	/// Storage: `Offences::ConcurrentReportsIndex` (r:1 w:1)
	/// Proof: `Offences::ConcurrentReportsIndex` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Offences::Reports` (r:1 w:1)
	/// Proof: `Offences::Reports` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ActiveEra` (r:1 w:0)
	/// Proof: `Staking::ActiveEra` (`max_values`: Some(1), `max_size`: Some(13), added: 508, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStartSessionIndex` (r:1 w:0)
	/// Proof: `Staking::ErasStartSessionIndex` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Invulnerables` (r:1 w:0)
	/// Proof: `Staking::Invulnerables` (`max_values`: Some(1), `max_size`: Some(641), added: 1136, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStakersOverview` (r:1 w:0)
	/// Proof: `Staking::ErasStakersOverview` (`max_values`: None, `max_size`: Some(92), added: 2567, mode: `MaxEncodedLen`)
	/// Storage: `Session::DisabledValidators` (r:1 w:1)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::Validators` (r:1 w:0)
	/// Proof: `Session::Validators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ValidatorSlashInEra` (r:1 w:1)
	/// Proof: `Staking::ValidatorSlashInEra` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `Staking::OffenceQueue` (r:1 w:1)
	/// Proof: `Staking::OffenceQueue` (`max_values`: None, `max_size`: Some(101), added: 2576, mode: `MaxEncodedLen`)
	/// Storage: `Staking::OffenceQueueEras` (r:1 w:1)
	/// Proof: `Staking::OffenceQueueEras` (`max_values`: Some(1), `max_size`: Some(2690), added: 3185, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 16]`.
	fn report_offence_grandpa(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `424`
		//  Estimated: `4175 + n * (1 ±0)`
		// Minimum execution time: 39_700_000 picoseconds.
		Weight::from_parts(41_685_972, 4175)
			// Standard Error: 5_328
			.saturating_add(Weight::from_parts(449_149, 0).saturating_mul(n.into()))
			.saturating_add(RocksDbWeight::get().reads(11_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
			.saturating_add(Weight::from_parts(0, 1).saturating_mul(n.into()))
	}
	/// Storage: `Offences::ConcurrentReportsIndex` (r:1 w:1)
	/// Proof: `Offences::ConcurrentReportsIndex` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Offences::Reports` (r:1 w:1)
	/// Proof: `Offences::Reports` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ActiveEra` (r:1 w:0)
	/// Proof: `Staking::ActiveEra` (`max_values`: Some(1), `max_size`: Some(13), added: 508, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStartSessionIndex` (r:1 w:0)
	/// Proof: `Staking::ErasStartSessionIndex` (`max_values`: None, `max_size`: Some(16), added: 2491, mode: `MaxEncodedLen`)
	/// Storage: `Staking::Invulnerables` (r:1 w:0)
	/// Proof: `Staking::Invulnerables` (`max_values`: Some(1), `max_size`: Some(641), added: 1136, mode: `MaxEncodedLen`)
	/// Storage: `Staking::ErasStakersOverview` (r:1 w:0)
	/// Proof: `Staking::ErasStakersOverview` (`max_values`: None, `max_size`: Some(92), added: 2567, mode: `MaxEncodedLen`)
	/// Storage: `Session::DisabledValidators` (r:1 w:1)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::Validators` (r:1 w:0)
	/// Proof: `Session::Validators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Staking::ValidatorSlashInEra` (r:1 w:1)
	/// Proof: `Staking::ValidatorSlashInEra` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `Staking::OffenceQueue` (r:1 w:1)
	/// Proof: `Staking::OffenceQueue` (`max_values`: None, `max_size`: Some(101), added: 2576, mode: `MaxEncodedLen`)
	/// Storage: `Staking::OffenceQueueEras` (r:1 w:1)
	/// Proof: `Staking::OffenceQueueEras` (`max_values`: Some(1), `max_size`: Some(2690), added: 3185, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 16]`.
	fn report_offence_babe(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `424`
		//  Estimated: `4175 + n * (1 ±0)`
		// Minimum execution time: 39_468_000 picoseconds.
		Weight::from_parts(41_735_370, 4175)
			// Standard Error: 5_463
			.saturating_add(Weight::from_parts(397_177, 0).saturating_mul(n.into()))
			.saturating_add(RocksDbWeight::get().reads(11_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
			.saturating_add(Weight::from_parts(0, 1).saturating_mul(n.into()))
	}
}
