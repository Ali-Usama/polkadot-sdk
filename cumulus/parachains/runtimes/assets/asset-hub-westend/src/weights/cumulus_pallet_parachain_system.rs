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

//! Autogenerated weights for `cumulus_pallet_parachain_system`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-20, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `cf7bc4bf1f5d`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("asset-hub-westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=asset-hub-westend-dev
// --pallet=cumulus_pallet_parachain_system
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/assets/asset-hub-westend/src/weights
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

/// Weight functions for `cumulus_pallet_parachain_system`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> cumulus_pallet_parachain_system::WeightInfo for WeightInfo<T> {
	/// Storage: `ParachainSystem::LastDmqMqcHead` (r:1 w:1)
	/// Proof: `ParachainSystem::LastDmqMqcHead` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(5), added: 500, mode: `MaxEncodedLen`)
	/// Storage: `ParachainSystem::ProcessedDownwardMessages` (r:0 w:1)
	/// Proof: `ParachainSystem::ProcessedDownwardMessages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `MessageQueue::Pages` (r:0 w:1000)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105521), added: 107996, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 1000]`.
	fn enqueue_inbound_downward_messages(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `84`
		//  Estimated: `3517`
		// Minimum execution time: 2_910_000 picoseconds.
		Weight::from_parts(3_066_000, 0)
			.saturating_add(Weight::from_parts(0, 3517))
			// Standard Error: 43_586
			.saturating_add(Weight::from_parts(310_234_637, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(4))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(n.into())))
	}
}
