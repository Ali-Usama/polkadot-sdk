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

//! Autogenerated weights for `polkadot_runtime_parachains::paras_inherent`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `5d8802e9776e`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot
// benchmark
// pallet
// --extrinsic=*
// --chain=rococo-dev
// --pallet=polkadot_runtime_parachains::paras_inherent
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

/// Weight functions for `polkadot_runtime_parachains::paras_inherent`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> polkadot_runtime_parachains::paras_inherent::WeightInfo for WeightInfo<T> {
	/// Storage: `ParaInherent::Included` (r:1 w:1)
	/// Proof: `ParaInherent::Included` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::ParentHash` (r:1 w:0)
	/// Proof: `System::ParentHash` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `ParasShared::AllowedRelayParents` (r:1 w:1)
	/// Proof: `ParasShared::AllowedRelayParents` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ClaimQueue` (r:1 w:0)
	/// Proof: `ParaScheduler::ClaimQueue` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ValidatorGroups` (r:1 w:0)
	/// Proof: `ParaScheduler::ValidatorGroups` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Babe::AuthorVrfRandomness` (r:1 w:0)
	/// Proof: `Babe::AuthorVrfRandomness` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `ParaInherent::OnChainVotes` (r:1 w:1)
	/// Proof: `ParaInherent::OnChainVotes` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Frozen` (r:1 w:0)
	/// Proof: `ParasDisputes::Frozen` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaInclusion::V1` (r:1 w:0)
	/// Proof: `ParaInclusion::V1` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::SessionStartBlock` (r:1 w:0)
	/// Proof: `ParaScheduler::SessionStartBlock` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Initializer::BufferedSessionChanges` (r:1 w:0)
	/// Proof: `Initializer::BufferedSessionChanges` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorIndices` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorIndices` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::DisabledValidators` (r:1 w:0)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn enter_empty() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `42760`
		//  Estimated: `46225`
		// Minimum execution time: 220_934_000 picoseconds.
		Weight::from_parts(229_648_000, 0)
			.saturating_add(Weight::from_parts(0, 46225))
			.saturating_add(T::DbWeight::get().reads(15))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `ParaInherent::Included` (r:1 w:1)
	/// Proof: `ParaInherent::Included` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::ParentHash` (r:1 w:0)
	/// Proof: `System::ParentHash` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `ParasShared::AllowedRelayParents` (r:1 w:1)
	/// Proof: `ParasShared::AllowedRelayParents` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ClaimQueue` (r:1 w:1)
	/// Proof: `ParaScheduler::ClaimQueue` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ValidatorGroups` (r:1 w:0)
	/// Proof: `ParaScheduler::ValidatorGroups` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Babe::AuthorVrfRandomness` (r:1 w:0)
	/// Proof: `Babe::AuthorVrfRandomness` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `ParaSessionInfo::Sessions` (r:1 w:0)
	/// Proof: `ParaSessionInfo::Sessions` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Disputes` (r:1 w:1)
	/// Proof: `ParasDisputes::Disputes` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::BackersOnDisputes` (r:1 w:1)
	/// Proof: `ParasDisputes::BackersOnDisputes` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Included` (r:1 w:1)
	/// Proof: `ParasDisputes::Included` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParaInherent::OnChainVotes` (r:1 w:1)
	/// Proof: `ParaInherent::OnChainVotes` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Frozen` (r:1 w:0)
	/// Proof: `ParasDisputes::Frozen` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaInclusion::V1` (r:2 w:1)
	/// Proof: `ParaInclusion::V1` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DownwardMessageQueues` (r:1 w:1)
	/// Proof: `Dmp::DownwardMessageQueues` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DeliveryFeeFactor` (r:1 w:1)
	/// Proof: `Dmp::DeliveryFeeFactor` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Hrmp::HrmpChannelDigests` (r:1 w:1)
	/// Proof: `Hrmp::HrmpChannelDigests` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::FutureCodeUpgrades` (r:1 w:0)
	/// Proof: `Paras::FutureCodeUpgrades` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Registrar::Paras` (r:1 w:0)
	/// Proof: `Registrar::Paras` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::SessionStartBlock` (r:1 w:0)
	/// Proof: `ParaScheduler::SessionStartBlock` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Initializer::BufferedSessionChanges` (r:1 w:0)
	/// Proof: `Initializer::BufferedSessionChanges` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorIndices` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorIndices` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::DisabledValidators` (r:1 w:0)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `CoretimeAssignmentProvider::CoreDescriptors` (r:1 w:1)
	/// Proof: `CoretimeAssignmentProvider::CoreDescriptors` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Hrmp::HrmpWatermarks` (r:0 w:1)
	/// Proof: `Hrmp::HrmpWatermarks` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::Heads` (r:0 w:1)
	/// Proof: `Paras::Heads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::UpgradeGoAheadSignal` (r:0 w:1)
	/// Proof: `Paras::UpgradeGoAheadSignal` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::MostRecentContext` (r:0 w:1)
	/// Proof: `Paras::MostRecentContext` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `v` is `[400, 1024]`.
	fn enter_variable_disputes(v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `203038`
		//  Estimated: `208978`
		// Minimum execution time: 17_732_662_000 picoseconds.
		Weight::from_parts(931_268_742, 0)
			.saturating_add(Weight::from_parts(0, 208978))
			// Standard Error: 9_127
			.saturating_add(Weight::from_parts(42_196_027, 0).saturating_mul(v.into()))
			.saturating_add(T::DbWeight::get().reads(26))
			.saturating_add(T::DbWeight::get().writes(16))
	}
	/// Storage: `ParaInherent::Included` (r:1 w:1)
	/// Proof: `ParaInherent::Included` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::ParentHash` (r:1 w:0)
	/// Proof: `System::ParentHash` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `ParasShared::AllowedRelayParents` (r:1 w:1)
	/// Proof: `ParasShared::AllowedRelayParents` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ClaimQueue` (r:1 w:0)
	/// Proof: `ParaScheduler::ClaimQueue` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ValidatorGroups` (r:1 w:0)
	/// Proof: `ParaScheduler::ValidatorGroups` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Babe::AuthorVrfRandomness` (r:1 w:0)
	/// Proof: `Babe::AuthorVrfRandomness` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `ParaInherent::OnChainVotes` (r:1 w:1)
	/// Proof: `ParaInherent::OnChainVotes` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Frozen` (r:1 w:0)
	/// Proof: `ParasDisputes::Frozen` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaInclusion::V1` (r:2 w:1)
	/// Proof: `ParaInclusion::V1` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::SessionStartBlock` (r:1 w:0)
	/// Proof: `ParaScheduler::SessionStartBlock` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Initializer::BufferedSessionChanges` (r:1 w:0)
	/// Proof: `Initializer::BufferedSessionChanges` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorIndices` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorIndices` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::DisabledValidators` (r:1 w:0)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn enter_bitfields() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76066`
		//  Estimated: `82006`
		// Minimum execution time: 502_697_000 picoseconds.
		Weight::from_parts(518_189_000, 0)
			.saturating_add(Weight::from_parts(0, 82006))
			.saturating_add(T::DbWeight::get().reads(16))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `ParaInherent::Included` (r:1 w:1)
	/// Proof: `ParaInherent::Included` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::ParentHash` (r:1 w:0)
	/// Proof: `System::ParentHash` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `ParasShared::AllowedRelayParents` (r:1 w:1)
	/// Proof: `ParasShared::AllowedRelayParents` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ClaimQueue` (r:1 w:1)
	/// Proof: `ParaScheduler::ClaimQueue` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ValidatorGroups` (r:1 w:0)
	/// Proof: `ParaScheduler::ValidatorGroups` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Babe::AuthorVrfRandomness` (r:1 w:0)
	/// Proof: `Babe::AuthorVrfRandomness` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `ParaInherent::OnChainVotes` (r:1 w:1)
	/// Proof: `ParaInherent::OnChainVotes` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Frozen` (r:1 w:0)
	/// Proof: `ParasDisputes::Frozen` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaInclusion::V1` (r:2 w:1)
	/// Proof: `ParaInclusion::V1` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DownwardMessageQueues` (r:1 w:1)
	/// Proof: `Dmp::DownwardMessageQueues` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DeliveryFeeFactor` (r:1 w:1)
	/// Proof: `Dmp::DeliveryFeeFactor` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Hrmp::HrmpChannelDigests` (r:1 w:1)
	/// Proof: `Hrmp::HrmpChannelDigests` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::FutureCodeUpgrades` (r:1 w:0)
	/// Proof: `Paras::FutureCodeUpgrades` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Registrar::Paras` (r:1 w:0)
	/// Proof: `Registrar::Paras` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Disputes` (r:1 w:0)
	/// Proof: `ParasDisputes::Disputes` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::SessionStartBlock` (r:1 w:0)
	/// Proof: `ParaScheduler::SessionStartBlock` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Initializer::BufferedSessionChanges` (r:1 w:0)
	/// Proof: `Initializer::BufferedSessionChanges` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::CurrentCodeHash` (r:1 w:0)
	/// Proof: `Paras::CurrentCodeHash` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::ParaLifecycles` (r:1 w:0)
	/// Proof: `Paras::ParaLifecycles` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:0)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	/// Storage: `ParasShared::ActiveValidatorIndices` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorIndices` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::DisabledValidators` (r:1 w:0)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `CoretimeAssignmentProvider::CoreDescriptors` (r:1 w:1)
	/// Proof: `CoretimeAssignmentProvider::CoreDescriptors` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Included` (r:0 w:1)
	/// Proof: `ParasDisputes::Included` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Hrmp::HrmpWatermarks` (r:0 w:1)
	/// Proof: `Hrmp::HrmpWatermarks` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::Heads` (r:0 w:1)
	/// Proof: `Paras::Heads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::UpgradeGoAheadSignal` (r:0 w:1)
	/// Proof: `Paras::UpgradeGoAheadSignal` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::MostRecentContext` (r:0 w:1)
	/// Proof: `Paras::MostRecentContext` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `v` is `[2, 3]`.
	fn enter_backed_candidates_variable(v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76725`
		//  Estimated: `82665`
		// Minimum execution time: 1_882_330_000 picoseconds.
		Weight::from_parts(1_935_790_063, 0)
			.saturating_add(Weight::from_parts(0, 82665))
			// Standard Error: 2_379_326
			.saturating_add(Weight::from_parts(233_512, 0).saturating_mul(v.into()))
			.saturating_add(T::DbWeight::get().reads(26))
			.saturating_add(T::DbWeight::get().writes(14))
	}
	/// Storage: `ParaInherent::Included` (r:1 w:1)
	/// Proof: `ParaInherent::Included` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::ParentHash` (r:1 w:0)
	/// Proof: `System::ParentHash` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `ParasShared::AllowedRelayParents` (r:1 w:1)
	/// Proof: `ParasShared::AllowedRelayParents` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ClaimQueue` (r:1 w:1)
	/// Proof: `ParaScheduler::ClaimQueue` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::ValidatorGroups` (r:1 w:0)
	/// Proof: `ParaScheduler::ValidatorGroups` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Babe::AuthorVrfRandomness` (r:1 w:0)
	/// Proof: `Babe::AuthorVrfRandomness` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `ParaInherent::OnChainVotes` (r:1 w:1)
	/// Proof: `ParaInherent::OnChainVotes` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Frozen` (r:1 w:0)
	/// Proof: `ParasDisputes::Frozen` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParaInclusion::V1` (r:2 w:1)
	/// Proof: `ParaInclusion::V1` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DownwardMessageQueues` (r:1 w:1)
	/// Proof: `Dmp::DownwardMessageQueues` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Dmp::DeliveryFeeFactor` (r:1 w:1)
	/// Proof: `Dmp::DeliveryFeeFactor` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Hrmp::HrmpChannelDigests` (r:1 w:1)
	/// Proof: `Hrmp::HrmpChannelDigests` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::FutureCodeUpgrades` (r:1 w:0)
	/// Proof: `Paras::FutureCodeUpgrades` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Registrar::Paras` (r:1 w:0)
	/// Proof: `Registrar::Paras` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Disputes` (r:1 w:0)
	/// Proof: `ParasDisputes::Disputes` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParaScheduler::SessionStartBlock` (r:1 w:0)
	/// Proof: `ParaScheduler::SessionStartBlock` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Initializer::BufferedSessionChanges` (r:1 w:0)
	/// Proof: `Initializer::BufferedSessionChanges` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::CurrentCodeHash` (r:1 w:0)
	/// Proof: `Paras::CurrentCodeHash` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::FutureCodeHash` (r:1 w:0)
	/// Proof: `Paras::FutureCodeHash` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::UpgradeRestrictionSignal` (r:1 w:0)
	/// Proof: `Paras::UpgradeRestrictionSignal` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::ParaLifecycles` (r:1 w:0)
	/// Proof: `Paras::ParaLifecycles` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:0)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	/// Storage: `ParasShared::ActiveValidatorIndices` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorIndices` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Session::DisabledValidators` (r:1 w:0)
	/// Proof: `Session::DisabledValidators` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `CoretimeAssignmentProvider::CoreDescriptors` (r:1 w:1)
	/// Proof: `CoretimeAssignmentProvider::CoreDescriptors` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParasDisputes::Included` (r:0 w:1)
	/// Proof: `ParasDisputes::Included` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Hrmp::HrmpWatermarks` (r:0 w:1)
	/// Proof: `Hrmp::HrmpWatermarks` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::Heads` (r:0 w:1)
	/// Proof: `Paras::Heads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::UpgradeGoAheadSignal` (r:0 w:1)
	/// Proof: `Paras::UpgradeGoAheadSignal` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::MostRecentContext` (r:0 w:1)
	/// Proof: `Paras::MostRecentContext` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn enter_backed_candidate_code_upgrade() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76738`
		//  Estimated: `82678`
		// Minimum execution time: 40_160_660_000 picoseconds.
		Weight::from_parts(41_081_072_000, 0)
			.saturating_add(Weight::from_parts(0, 82678))
			.saturating_add(T::DbWeight::get().reads(28))
			.saturating_add(T::DbWeight::get().writes(14))
	}
}
