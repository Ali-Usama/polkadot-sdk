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

//! Autogenerated weights for `pallet_message_queue`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-20, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `daa8aefba48e`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("bridge-hub-westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=bridge-hub-westend-dev
// --pallet=pallet_message_queue
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/bridge-hubs/bridge-hub-westend/src/weights
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

/// Weight functions for `pallet_message_queue`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_message_queue::WeightInfo for WeightInfo<T> {
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:0)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::BookStateFor` (r:2 w:2)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	fn ready_ring_knit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `223`
		//  Estimated: `6212`
		// Minimum execution time: 13_754_000 picoseconds.
		Weight::from_parts(14_220_000, 0)
			.saturating_add(Weight::from_parts(0, 6212))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:2 w:2)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	fn ready_ring_unknit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `218`
		//  Estimated: `6212`
		// Minimum execution time: 12_486_000 picoseconds.
		Weight::from_parts(13_284_000, 0)
			.saturating_add(Weight::from_parts(0, 6212))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	fn service_queue_base() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6`
		//  Estimated: `3601`
		// Minimum execution time: 4_258_000 picoseconds.
		Weight::from_parts(4_550_000, 0)
			.saturating_add(Weight::from_parts(0, 3601))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn service_page_base_completion() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `72`
		//  Estimated: `109014`
		// Minimum execution time: 6_558_000 picoseconds.
		Weight::from_parts(6_860_000, 0)
			.saturating_add(Weight::from_parts(0, 109014))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn service_page_base_no_completion() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `72`
		//  Estimated: `109014`
		// Minimum execution time: 6_901_000 picoseconds.
		Weight::from_parts(7_208_000, 0)
			.saturating_add(Weight::from_parts(0, 109014))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:0 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:0 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn service_page_item() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 282_813_000 picoseconds.
		Weight::from_parts(291_770_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:0)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	fn bump_service_head() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `171`
		//  Estimated: `3601`
		// Minimum execution time: 8_093_000 picoseconds.
		Weight::from_parts(8_361_000, 0)
			.saturating_add(Weight::from_parts(0, 3601))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn reap_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `105609`
		//  Estimated: `109014`
		// Minimum execution time: 87_631_000 picoseconds.
		Weight::from_parts(89_736_000, 0)
			.saturating_add(Weight::from_parts(0, 109014))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn execute_overweight_page_removed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `105609`
		//  Estimated: `109014`
		// Minimum execution time: 115_506_000 picoseconds.
		Weight::from_parts(117_336_000, 0)
			.saturating_add(Weight::from_parts(0, 109014))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn execute_overweight_page_updated() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `105609`
		//  Estimated: `109014`
		// Minimum execution time: 185_268_000 picoseconds.
		Weight::from_parts(190_929_000, 0)
			.saturating_add(Weight::from_parts(0, 109014))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
}
