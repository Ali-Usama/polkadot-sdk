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

//! Autogenerated weights for `snowbridge_pallet_outbound_queue`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `4b641a4a9b9d`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("bridge-hub-rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=bridge-hub-rococo-dev
// --pallet=snowbridge_pallet_outbound_queue
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/bridge-hubs/bridge-hub-rococo/src/weights
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

/// Weight functions for `snowbridge_pallet_outbound_queue`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> snowbridge_pallet_outbound_queue::WeightInfo for WeightInfo<T> {
	/// Storage: `EthereumOutboundQueue::MessageLeaves` (r:1 w:1)
	/// Proof: `EthereumOutboundQueue::MessageLeaves` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `EthereumOutboundQueue::Nonce` (r:1 w:1)
	/// Proof: `EthereumOutboundQueue::Nonce` (`max_values`: None, `max_size`: Some(48), added: 2523, mode: `MaxEncodedLen`)
	/// Storage: `EthereumSystem::PricingParameters` (r:1 w:0)
	/// Proof: `EthereumSystem::PricingParameters` (`max_values`: Some(1), `max_size`: Some(112), added: 607, mode: `MaxEncodedLen`)
	/// Storage: `EthereumOutboundQueue::Messages` (r:1 w:1)
	/// Proof: `EthereumOutboundQueue::Messages` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn do_process_message() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `80`
		//  Estimated: `3513`
		// Minimum execution time: 34_742_000 picoseconds.
		Weight::from_parts(35_506_000, 0)
			.saturating_add(Weight::from_parts(0, 3513))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `EthereumOutboundQueue::MessageLeaves` (r:1 w:0)
	/// Proof: `EthereumOutboundQueue::MessageLeaves` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn commit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1057`
		//  Estimated: `2542`
		// Minimum execution time: 29_425_000 picoseconds.
		Weight::from_parts(30_040_000, 0)
			.saturating_add(Weight::from_parts(0, 2542))
			.saturating_add(T::DbWeight::get().reads(1))
	}
	/// Storage: `EthereumOutboundQueue::MessageLeaves` (r:1 w:0)
	/// Proof: `EthereumOutboundQueue::MessageLeaves` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	fn commit_single() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `64`
		//  Estimated: `1549`
		// Minimum execution time: 9_502_000 picoseconds.
		Weight::from_parts(9_905_000, 0)
			.saturating_add(Weight::from_parts(0, 1549))
			.saturating_add(T::DbWeight::get().reads(1))
	}
}
