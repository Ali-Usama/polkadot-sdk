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

//! Autogenerated weights for `pallet_conviction_voting`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-30, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `972230656fc2`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/westend-runtime/westend_runtime.wasm
// --pallet=pallet_conviction_voting
// --header=/__w/polkadot-sdk/polkadot-sdk/polkadot/file_header.txt
// --output=./polkadot/runtime/westend/src/weights
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

/// Weight functions for `pallet_conviction_voting`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_conviction_voting::WeightInfo for WeightInfo<T> {
	/// Storage: `Referenda::ReferendumInfoFor` (r:1 w:1)
	/// Proof: `Referenda::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(936), added: 3411, mode: `MaxEncodedLen`)
	/// Storage: `ConvictionVoting::VotingFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::VotingFor` (`max_values`: None, `max_size`: Some(27241), added: 29716, mode: `MaxEncodedLen`)
	/// Storage: `ConvictionVoting::ClassLocksFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::ClassLocksFor` (`max_values`: None, `max_size`: Some(311), added: 2786, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Locks` (r:1 w:1)
	/// Proof: `Balances::Locks` (`max_values`: None, `max_size`: Some(1299), added: 3774, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Freezes` (r:1 w:0)
	/// Proof: `Balances::Freezes` (`max_values`: None, `max_size`: Some(67), added: 2542, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Agenda` (r:1 w:1)
	/// Proof: `Scheduler::Agenda` (`max_values`: None, `max_size`: Some(38963), added: 41438, mode: `MaxEncodedLen`)
	fn vote_new() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `13408`
		//  Estimated: `42428`
		// Minimum execution time: 124_976_000 picoseconds.
		Weight::from_parts(132_967_000, 0)
			.saturating_add(Weight::from_parts(0, 42428))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `Referenda::ReferendumInfoFor` (r:1 w:1)
	/// Proof: `Referenda::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(936), added: 3411, mode: `MaxEncodedLen`)
	/// Storage: `ConvictionVoting::VotingFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::VotingFor` (`max_values`: None, `max_size`: Some(27241), added: 29716, mode: `MaxEncodedLen`)
	/// Storage: `ConvictionVoting::ClassLocksFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::ClassLocksFor` (`max_values`: None, `max_size`: Some(311), added: 2786, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Locks` (r:1 w:1)
	/// Proof: `Balances::Locks` (`max_values`: None, `max_size`: Some(1299), added: 3774, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Freezes` (r:1 w:0)
	/// Proof: `Balances::Freezes` (`max_values`: None, `max_size`: Some(67), added: 2542, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Agenda` (r:2 w:2)
	/// Proof: `Scheduler::Agenda` (`max_values`: None, `max_size`: Some(38963), added: 41438, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Retries` (r:0 w:1)
	/// Proof: `Scheduler::Retries` (`max_values`: None, `max_size`: Some(30), added: 2505, mode: `MaxEncodedLen`)
	fn vote_existing() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `14129`
		//  Estimated: `83866`
		// Minimum execution time: 152_462_000 picoseconds.
		Weight::from_parts(160_558_000, 0)
			.saturating_add(Weight::from_parts(0, 83866))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(7))
	}
	/// Storage: `ConvictionVoting::VotingFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::VotingFor` (`max_values`: None, `max_size`: Some(27241), added: 29716, mode: `MaxEncodedLen`)
	/// Storage: `Referenda::ReferendumInfoFor` (r:1 w:1)
	/// Proof: `Referenda::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(936), added: 3411, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Agenda` (r:2 w:2)
	/// Proof: `Scheduler::Agenda` (`max_values`: None, `max_size`: Some(38963), added: 41438, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Retries` (r:0 w:1)
	/// Proof: `Scheduler::Retries` (`max_values`: None, `max_size`: Some(30), added: 2505, mode: `MaxEncodedLen`)
	fn remove_vote() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `13918`
		//  Estimated: `83866`
		// Minimum execution time: 125_750_000 picoseconds.
		Weight::from_parts(131_616_000, 0)
			.saturating_add(Weight::from_parts(0, 83866))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `ConvictionVoting::VotingFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::VotingFor` (`max_values`: None, `max_size`: Some(27241), added: 29716, mode: `MaxEncodedLen`)
	/// Storage: `Referenda::ReferendumInfoFor` (r:1 w:0)
	/// Proof: `Referenda::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(936), added: 3411, mode: `MaxEncodedLen`)
	fn remove_other_vote() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `13005`
		//  Estimated: `30706`
		// Minimum execution time: 68_640_000 picoseconds.
		Weight::from_parts(75_376_000, 0)
			.saturating_add(Weight::from_parts(0, 30706))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `ConvictionVoting::VotingFor` (r:2 w:2)
	/// Proof: `ConvictionVoting::VotingFor` (`max_values`: None, `max_size`: Some(27241), added: 29716, mode: `MaxEncodedLen`)
	/// Storage: `Referenda::ReferendumInfoFor` (r:512 w:512)
	/// Proof: `Referenda::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(936), added: 3411, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Agenda` (r:2 w:2)
	/// Proof: `Scheduler::Agenda` (`max_values`: None, `max_size`: Some(38963), added: 41438, mode: `MaxEncodedLen`)
	/// Storage: `ConvictionVoting::ClassLocksFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::ClassLocksFor` (`max_values`: None, `max_size`: Some(311), added: 2786, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Locks` (r:1 w:1)
	/// Proof: `Balances::Locks` (`max_values`: None, `max_size`: Some(1299), added: 3774, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Freezes` (r:1 w:0)
	/// Proof: `Balances::Freezes` (`max_values`: None, `max_size`: Some(67), added: 2542, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Retries` (r:0 w:50)
	/// Proof: `Scheduler::Retries` (`max_values`: None, `max_size`: Some(30), added: 2505, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[0, 512]`.
	fn delegate(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `29603 + r * (365 ±0)`
		//  Estimated: `83866 + r * (3411 ±0)`
		// Minimum execution time: 60_273_000 picoseconds.
		Weight::from_parts(869_442_278, 0)
			.saturating_add(Weight::from_parts(0, 83866))
			// Standard Error: 63_979
			.saturating_add(Weight::from_parts(22_051_717, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(r.into())))
			.saturating_add(T::DbWeight::get().writes(45))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(r.into())))
			.saturating_add(Weight::from_parts(0, 3411).saturating_mul(r.into()))
	}
	/// Storage: `ConvictionVoting::VotingFor` (r:2 w:2)
	/// Proof: `ConvictionVoting::VotingFor` (`max_values`: None, `max_size`: Some(27241), added: 29716, mode: `MaxEncodedLen`)
	/// Storage: `Referenda::ReferendumInfoFor` (r:512 w:512)
	/// Proof: `Referenda::ReferendumInfoFor` (`max_values`: None, `max_size`: Some(936), added: 3411, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Agenda` (r:2 w:2)
	/// Proof: `Scheduler::Agenda` (`max_values`: None, `max_size`: Some(38963), added: 41438, mode: `MaxEncodedLen`)
	/// Storage: `Scheduler::Retries` (r:0 w:50)
	/// Proof: `Scheduler::Retries` (`max_values`: None, `max_size`: Some(30), added: 2505, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[0, 512]`.
	fn undelegate(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `29555 + r * (365 ±0)`
		//  Estimated: `83866 + r * (3411 ±0)`
		// Minimum execution time: 36_328_000 picoseconds.
		Weight::from_parts(825_505_499, 0)
			.saturating_add(Weight::from_parts(0, 83866))
			// Standard Error: 62_718
			.saturating_add(Weight::from_parts(22_004_057, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(r.into())))
			.saturating_add(T::DbWeight::get().writes(43))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(r.into())))
			.saturating_add(Weight::from_parts(0, 3411).saturating_mul(r.into()))
	}
	/// Storage: `ConvictionVoting::VotingFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::VotingFor` (`max_values`: None, `max_size`: Some(27241), added: 29716, mode: `MaxEncodedLen`)
	/// Storage: `ConvictionVoting::ClassLocksFor` (r:1 w:1)
	/// Proof: `ConvictionVoting::ClassLocksFor` (`max_values`: None, `max_size`: Some(311), added: 2786, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Locks` (r:1 w:1)
	/// Proof: `Balances::Locks` (`max_values`: None, `max_size`: Some(1299), added: 3774, mode: `MaxEncodedLen`)
	/// Storage: `Balances::Freezes` (r:1 w:0)
	/// Proof: `Balances::Freezes` (`max_values`: None, `max_size`: Some(67), added: 2542, mode: `MaxEncodedLen`)
	fn unlock() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `12181`
		//  Estimated: `30706`
		// Minimum execution time: 93_367_000 picoseconds.
		Weight::from_parts(101_338_000, 0)
			.saturating_add(Weight::from_parts(0, 30706))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
}
