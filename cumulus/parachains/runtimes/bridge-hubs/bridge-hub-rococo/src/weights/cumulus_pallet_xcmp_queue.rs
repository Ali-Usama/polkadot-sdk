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

//! Autogenerated weights for `cumulus_pallet_xcmp_queue`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-30, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `569cf895a746`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/bridge-hub-rococo-runtime/bridge_hub_rococo_runtime.wasm
// --pallet=cumulus_pallet_xcmp_queue
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

/// Weight functions for `cumulus_pallet_xcmp_queue`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> cumulus_pallet_xcmp_queue::WeightInfo for WeightInfo<T> {
	/// Storage: `XcmpQueue::QueueConfig` (r:1 w:1)
	/// Proof: `XcmpQueue::QueueConfig` (`max_values`: Some(1), `max_size`: Some(12), added: 507, mode: `MaxEncodedLen`)
	fn set_config_with_u32() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4`
		//  Estimated: `1497`
		// Minimum execution time: 4_563_000 picoseconds.
		Weight::from_parts(4_924_000, 0)
			.saturating_add(Weight::from_parts(0, 1497))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `XcmpQueue::QueueConfig` (r:1 w:0)
	/// Proof: `XcmpQueue::QueueConfig` (`max_values`: Some(1), `max_size`: Some(12), added: 507, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::InboundXcmpSuspended` (r:1 w:0)
	/// Proof: `XcmpQueue::InboundXcmpSuspended` (`max_values`: Some(1), `max_size`: Some(4002), added: 4497, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:0 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn enqueue_xcmp_message() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `80`
		//  Estimated: `5487`
		// Minimum execution time: 13_505_000 picoseconds.
		Weight::from_parts(14_024_000, 0)
			.saturating_add(Weight::from_parts(0, 5487))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `XcmpQueue::OutboundXcmpStatus` (r:1 w:1)
	/// Proof: `XcmpQueue::OutboundXcmpStatus` (`max_values`: Some(1), `max_size`: Some(1282), added: 1777, mode: `MaxEncodedLen`)
	fn suspend_channel() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `4`
		//  Estimated: `2767`
		// Minimum execution time: 2_694_000 picoseconds.
		Weight::from_parts(2_854_000, 0)
			.saturating_add(Weight::from_parts(0, 2767))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `XcmpQueue::OutboundXcmpStatus` (r:1 w:1)
	/// Proof: `XcmpQueue::OutboundXcmpStatus` (`max_values`: Some(1), `max_size`: Some(1282), added: 1777, mode: `MaxEncodedLen`)
	fn resume_channel() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `39`
		//  Estimated: `2767`
		// Minimum execution time: 4_118_000 picoseconds.
		Weight::from_parts(4_206_000, 0)
			.saturating_add(Weight::from_parts(0, 2767))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	fn take_first_concatenated_xcm() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 10_324_000 picoseconds.
		Weight::from_parts(10_526_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	/// Storage: UNKNOWN KEY `0x7b3237373ffdfeb1cab4222e3b520d6b345d8e88afa015075c945637c07e8f20` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0x7b3237373ffdfeb1cab4222e3b520d6b345d8e88afa015075c945637c07e8f20` (r:1 w:1)
	/// Storage: UNKNOWN KEY `0x7b3237373ffdfeb1cab4222e3b520d6bedc49980ba3aa32b0a189290fd036649` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0x7b3237373ffdfeb1cab4222e3b520d6bedc49980ba3aa32b0a189290fd036649` (r:1 w:1)
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::QueueConfig` (r:1 w:0)
	/// Proof: `XcmpQueue::QueueConfig` (`max_values`: Some(1), `max_size`: Some(12), added: 507, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::InboundXcmpSuspended` (r:1 w:0)
	/// Proof: `XcmpQueue::InboundXcmpSuspended` (`max_values`: Some(1), `max_size`: Some(4002), added: 4497, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:0 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn on_idle_good_msg() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `105645`
		//  Estimated: `109110`
		// Minimum execution time: 183_023_000 picoseconds.
		Weight::from_parts(189_446_000, 0)
			.saturating_add(Weight::from_parts(0, 109110))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: UNKNOWN KEY `0x7b3237373ffdfeb1cab4222e3b520d6b345d8e88afa015075c945637c07e8f20` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0x7b3237373ffdfeb1cab4222e3b520d6b345d8e88afa015075c945637c07e8f20` (r:1 w:1)
	/// Storage: UNKNOWN KEY `0x7b3237373ffdfeb1cab4222e3b520d6bedc49980ba3aa32b0a189290fd036649` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0x7b3237373ffdfeb1cab4222e3b520d6bedc49980ba3aa32b0a189290fd036649` (r:1 w:1)
	/// Storage: `MessageQueue::BookStateFor` (r:1 w:1)
	/// Proof: `MessageQueue::BookStateFor` (`max_values`: None, `max_size`: Some(136), added: 2611, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::ServiceHead` (r:1 w:1)
	/// Proof: `MessageQueue::ServiceHead` (`max_values`: Some(1), `max_size`: Some(33), added: 528, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::QueueConfig` (r:1 w:0)
	/// Proof: `XcmpQueue::QueueConfig` (`max_values`: Some(1), `max_size`: Some(12), added: 507, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::InboundXcmpSuspended` (r:1 w:0)
	/// Proof: `XcmpQueue::InboundXcmpSuspended` (`max_values`: Some(1), `max_size`: Some(4002), added: 4497, mode: `MaxEncodedLen`)
	/// Storage: `MessageQueue::Pages` (r:0 w:1)
	/// Proof: `MessageQueue::Pages` (`max_values`: None, `max_size`: Some(105549), added: 108024, mode: `MaxEncodedLen`)
	fn on_idle_large_msg() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `65714`
		//  Estimated: `69179`
		// Minimum execution time: 125_423_000 picoseconds.
		Weight::from_parts(127_183_000, 0)
			.saturating_add(Weight::from_parts(0, 69179))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(5))
	}
}
