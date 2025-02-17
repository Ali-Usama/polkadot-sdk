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

//! Autogenerated weights for `runtime_parachains::paras`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2024-02-29, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-bn-ce5rx-project-674-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("rococo-dev")`, DB CACHE: 1024

// Executed Command:
// ./target/production/polkadot
// benchmark
// pallet
// --chain=rococo-dev
// --steps=50
// --repeat=20
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --pallet=runtime_parachains::paras
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --header=./polkadot/file_header.txt
// --output=./polkadot/runtime/rococo/src/weights/runtime_parachains_paras.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::Weight};
use core::marker::PhantomData;

/// Weight functions for `runtime_parachains::paras`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> polkadot_runtime_parachains::paras::WeightInfo for WeightInfo<T> {
	/// Storage: Paras CurrentCodeHash (r:1 w:1)
	/// Proof Skipped: Paras CurrentCodeHash (max_values: None, max_size: None, mode: Measured)
	/// Storage: Paras CodeByHashRefs (r:1 w:1)
	/// Proof Skipped: Paras CodeByHashRefs (max_values: None, max_size: None, mode: Measured)
	/// Storage: Paras PastCodeMeta (r:1 w:1)
	/// Proof Skipped: Paras PastCodeMeta (max_values: None, max_size: None, mode: Measured)
	/// Storage: Paras PastCodePruning (r:1 w:1)
	/// Proof Skipped: Paras PastCodePruning (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Paras PastCodeHash (r:0 w:1)
	/// Proof Skipped: Paras PastCodeHash (max_values: None, max_size: None, mode: Measured)
	/// Storage: Paras CodeByHash (r:0 w:1)
	/// Proof Skipped: Paras CodeByHash (max_values: None, max_size: None, mode: Measured)
	/// The range of component `c` is `[1, 3145728]`.
	fn force_set_current_code(c: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `8309`
		//  Estimated: `11774`
		// Minimum execution time: 27_488_000 picoseconds.
		Weight::from_parts(27_810_000, 0)
			.saturating_add(Weight::from_parts(0, 11774))
			// Standard Error: 8
			.saturating_add(Weight::from_parts(2_189, 0).saturating_mul(c.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `Paras::Heads` (r:0 w:1)
	/// Proof: `Paras::Heads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `s` is `[1, 1048576]`.
	fn force_set_current_head(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_793_000 picoseconds.
		Weight::from_parts(7_987_606, 0)
			.saturating_add(Weight::from_parts(0, 0))
			// Standard Error: 1
			.saturating_add(Weight::from_parts(971, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Paras::MostRecentContext` (r:0 w:1)
	/// Proof: `Paras::MostRecentContext` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn force_set_most_recent_context() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_733_000 picoseconds.
		Weight::from_parts(2_954_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Paras::FutureCodeHash` (r:1 w:1)
	/// Proof: `Paras::FutureCodeHash` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::CurrentCodeHash` (r:1 w:0)
	/// Proof: `Paras::CurrentCodeHash` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::UpgradeCooldowns` (r:1 w:1)
	/// Proof: `Paras::UpgradeCooldowns` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteMap` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteMap` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::CodeByHash` (r:1 w:1)
	/// Proof: `Paras::CodeByHash` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteList` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteList` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::CodeByHashRefs` (r:1 w:1)
	/// Proof: `Paras::CodeByHashRefs` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::UpgradeRestrictionSignal` (r:0 w:1)
	/// Proof: `Paras::UpgradeRestrictionSignal` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `c` is `[1, 3145728]`.
	fn force_schedule_code_upgrade(c: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `8452`
		//  Estimated: `11917`
		// Minimum execution time: 6_072_000 picoseconds.
		Weight::from_parts(6_128_000, 0)
			.saturating_add(Weight::from_parts(0, 11917))
			// Standard Error: 2
			.saturating_add(Weight::from_parts(2_334, 0).saturating_mul(c.into()))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(6))
	}
	/// Storage: `Paras::FutureCodeUpgrades` (r:1 w:0)
	/// Proof: `Paras::FutureCodeUpgrades` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Registrar::Paras` (r:1 w:0)
	/// Proof: `Registrar::Paras` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::Heads` (r:0 w:1)
	/// Proof: `Paras::Heads` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::UpgradeGoAheadSignal` (r:0 w:1)
	/// Proof: `Paras::UpgradeGoAheadSignal` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::MostRecentContext` (r:0 w:1)
	/// Proof: `Paras::MostRecentContext` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `s` is `[1, 1048576]`.
	fn force_note_new_head(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `163`
		//  Estimated: `3628`
		// Minimum execution time: 15_166_000 picoseconds.
		Weight::from_parts(21_398_053, 0)
			.saturating_add(Weight::from_parts(0, 3628))
			// Standard Error: 1
			.saturating_add(Weight::from_parts(976, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::ActionsQueue` (r:1 w:1)
	/// Proof: `Paras::ActionsQueue` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn force_queue_action() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4312`
		//  Estimated: `7777`
		// Minimum execution time: 16_345_000 picoseconds.
		Weight::from_parts(16_712_000, 0)
			.saturating_add(Weight::from_parts(0, 7777))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Paras::PvfActiveVoteMap` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteMap` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteList` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteList` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::ActionsQueue` (r:1 w:1)
	/// Proof: `Paras::ActionsQueue` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `c` is `[1, 3145728]`.
	fn add_trusted_validation_code(c: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `683`
		//  Estimated: `4148`
		// Minimum execution time: 78_076_000 picoseconds.
		Weight::from_parts(123_193_814, 0)
			.saturating_add(Weight::from_parts(0, 4148))
			// Standard Error: 5
			.saturating_add(Weight::from_parts(1_770, 0).saturating_mul(c.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Paras::CodeByHashRefs` (r:1 w:0)
	/// Proof: `Paras::CodeByHashRefs` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::CodeByHash` (r:0 w:1)
	/// Proof: `Paras::CodeByHash` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn poke_unused_validation_code() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `28`
		//  Estimated: `3493`
		// Minimum execution time: 5_184_000 picoseconds.
		Weight::from_parts(5_430_000, 0)
			.saturating_add(Weight::from_parts(0, 3493))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteMap` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteMap` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn include_pvf_check_statement() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `26706`
		//  Estimated: `30171`
		// Minimum execution time: 102_995_000 picoseconds.
		Weight::from_parts(108_977_000, 0)
			.saturating_add(Weight::from_parts(0, 30171))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteMap` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteMap` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteList` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteList` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::UpcomingUpgrades` (r:1 w:1)
	/// Proof: `Paras::UpcomingUpgrades` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `System::Digest` (r:1 w:1)
	/// Proof: `System::Digest` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::FutureCodeUpgrades` (r:0 w:100)
	/// Proof: `Paras::FutureCodeUpgrades` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn include_pvf_check_statement_finalize_upgrade_accept() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `27360`
		//  Estimated: `30825`
		// Minimum execution time: 709_433_000 picoseconds.
		Weight::from_parts(725_074_000, 0)
			.saturating_add(Weight::from_parts(0, 30825))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(104))
	}
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteMap` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteMap` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn include_pvf_check_statement_finalize_upgrade_reject() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `27338`
		//  Estimated: `30803`
		// Minimum execution time: 98_973_000 picoseconds.
		Weight::from_parts(104_715_000, 0)
			.saturating_add(Weight::from_parts(0, 30803))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteMap` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteMap` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteList` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteList` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::ActionsQueue` (r:1 w:1)
	/// Proof: `Paras::ActionsQueue` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn include_pvf_check_statement_finalize_onboarding_accept() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `26728`
		//  Estimated: `30193`
		// Minimum execution time: 550_958_000 picoseconds.
		Weight::from_parts(564_497_000, 0)
			.saturating_add(Weight::from_parts(0, 30193))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `ParasShared::ActiveValidatorKeys` (r:1 w:0)
	/// Proof: `ParasShared::ActiveValidatorKeys` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `ParasShared::CurrentSessionIndex` (r:1 w:0)
	/// Proof: `ParasShared::CurrentSessionIndex` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Paras::PvfActiveVoteMap` (r:1 w:1)
	/// Proof: `Paras::PvfActiveVoteMap` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn include_pvf_check_statement_finalize_onboarding_reject() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `26706`
		//  Estimated: `30171`
		// Minimum execution time: 97_088_000 picoseconds.
		Weight::from_parts(103_617_000, 0)
			.saturating_add(Weight::from_parts(0, 30171))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	fn authorize_force_set_current_code_hash() -> Weight {
		// TODO: FAIL-CI fresh
		Weight::from_parts(120_274_000, 0)
			.saturating_add(Weight::from_parts(0, 30147))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	fn apply_authorized_force_set_current_code(c: u32, ) -> Weight {
		// TODO: FAIL-CI fresh
		Weight::from_parts(33_700_000, 0)
			.saturating_add(Weight::from_parts(0, 11774))
			// Standard Error: 10
			.saturating_add(Weight::from_parts(2_659, 0).saturating_mul(c.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(6))
	}
}
