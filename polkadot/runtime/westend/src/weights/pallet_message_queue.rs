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

//! Autogenerated weights for `pallet_message_queue`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `3a2e9ae8a8f5`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/westend-runtime/westend_runtime.wasm
// --pallet=pallet_message_queue
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

/// Weight functions for `pallet_message_queue`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_message_queue::WeightInfo for WeightInfo<T> {
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:0)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(6), added: 501, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::BookStateFor` (r:2 w:2)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	fn ready_ring_knit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `281`
		//  Estimated: `6050`
		// Minimum execution time: 16_991_000 picoseconds.
		Weight::from_parts(17_813_000, 0)
			.saturating_add(Weight::from_parts(0, 6050))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:2 w:2)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(6), added: 501, mode: `MaxEncodedLen`)
	fn ready_ring_unknit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `281`
		//  Estimated: `6050`
		// Minimum execution time: 16_268_000 picoseconds.
		Weight::from_parts(16_659_000, 0)
			.saturating_add(Weight::from_parts(0, 6050))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	fn service_queue_base() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `42`
		//  Estimated: `3520`
		// Minimum execution time: 4_901_000 picoseconds.
		Weight::from_parts(5_262_000, 0)
			.saturating_add(Weight::from_parts(0, 3520))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(131122), added: 133597, mode: `MaxEncodedLen`)
	fn service_page_base_completion() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `115`
		//  Estimated: `134587`
		// Minimum execution time: 10_587_000 picoseconds.
		Weight::from_parts(11_040_000, 0)
			.saturating_add(Weight::from_parts(0, 134587))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(131122), added: 133597, mode: `MaxEncodedLen`)
	fn service_page_base_no_completion() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `115`
		//  Estimated: `134587`
		// Minimum execution time: 10_729_000 picoseconds.
		Weight::from_parts(11_263_000, 0)
			.saturating_add(Weight::from_parts(0, 134587))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:0 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:0 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(131122), added: 133597, mode: `MaxEncodedLen`)
	fn service_page_item() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 381_300_000 picoseconds.
		Weight::from_parts(390_220_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(6), added: 501, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:0)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	fn bump_service_head() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `220`
		//  Estimated: `3520`
		// Minimum execution time: 12_503_000 picoseconds.
		Weight::from_parts(12_909_000, 0)
			.saturating_add(Weight::from_parts(0, 3520))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:0)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::ServiceHead` (r:0 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(6), added: 501, mode: `MaxEncodedLen`)
	fn set_service_head() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `220`
		//  Estimated: `3520`
		// Minimum execution time: 11_071_000 picoseconds.
		Weight::from_parts(11_553_000, 0)
			.saturating_add(Weight::from_parts(0, 3520))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(131122), added: 133597, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x3a72656c61795f64697370617463685f71756575655f72656d61696e696e675f` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a72656c61795f64697370617463685f71756575655f72656d61696e696e675f` (r:0 w:1)
	/// Storage: UNKNOWN KEY `0xf5207f03cfdce586301014700e2c2593fad157e461d71fd4c1f936839a5f1f3e` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0xf5207f03cfdce586301014700e2c2593fad157e461d71fd4c1f936839a5f1f3e` (r:0 w:1)
	fn reap_page() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `131252`
		//  Estimated: `134587`
		// Minimum execution time: 162_710_000 picoseconds.
		Weight::from_parts(166_261_000, 0)
			.saturating_add(Weight::from_parts(0, 134587))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(131122), added: 133597, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x3a72656c61795f64697370617463685f71756575655f72656d61696e696e675f` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a72656c61795f64697370617463685f71756575655f72656d61696e696e675f` (r:0 w:1)
	/// Storage: UNKNOWN KEY `0xf5207f03cfdce586301014700e2c2593fad157e461d71fd4c1f936839a5f1f3e` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0xf5207f03cfdce586301014700e2c2593fad157e461d71fd4c1f936839a5f1f3e` (r:0 w:1)
	fn execute_overweight_page_removed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `131252`
		//  Estimated: `134587`
		// Minimum execution time: 200_138_000 picoseconds.
		Weight::from_parts(210_177_000, 0)
			.saturating_add(Weight::from_parts(0, 134587))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(55), added: 2530, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:1 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(131122), added: 133597, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x3a72656c61795f64697370617463685f71756575655f72656d61696e696e675f` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0x3a72656c61795f64697370617463685f71756575655f72656d61696e696e675f` (r:0 w:1)
	/// Storage: UNKNOWN KEY `0xf5207f03cfdce586301014700e2c2593fad157e461d71fd4c1f936839a5f1f3e` (r:0 w:1)
	/// Proof: UNKNOWN KEY `0xf5207f03cfdce586301014700e2c2593fad157e461d71fd4c1f936839a5f1f3e` (r:0 w:1)
	fn execute_overweight_page_updated() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `131252`
		//  Estimated: `134587`
		// Minimum execution time: 275_951_000 picoseconds.
		Weight::from_parts(284_857_000, 0)
			.saturating_add(Weight::from_parts(0, 134587))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(4))
	}
}
