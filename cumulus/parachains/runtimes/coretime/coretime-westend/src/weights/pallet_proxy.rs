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

//! Autogenerated weights for `pallet_proxy`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-30, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `576ddb596147`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/coretime-westend-runtime/coretime_westend_runtime.wasm
// --pallet=pallet_proxy
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/coretime/coretime-westend/src/weights
// --wasm-execution=compiled
// --steps=50
// --repeat=20
// --heap-pages=4096
// --no-storage-info
// --no-min-squares
// --no-median-slopes
// --genesis-builder-policy=none
// --exclude-pallets=pallet_xcm,pallet_xcm_benchmarks::fungible,pallet_xcm_benchmarks::generic

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::Weight};
use core::marker::PhantomData;

/// Weight functions for `pallet_proxy`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_proxy::WeightInfo for WeightInfo<T> {
	/// Storage: `Proxy::Proxies` (r:1 w:0)
	/// Proof: `Proxy::Proxies` (`max_values`: None, `max_size`: Some(1241), added: 3716, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[1, 31]`.
	fn proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `65 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 11_979_000 picoseconds.
		Weight::from_parts(12_760_013, 0)
			.saturating_add(Weight::from_parts(0, 4706))
			// Standard Error: 879
			.saturating_add(Weight::from_parts(36_866, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1))
	}
	/// Storage: `Proxy::Proxies` (r:1 w:0)
	/// Proof: `Proxy::Proxies` (`max_values`: None, `max_size`: Some(1241), added: 3716, mode: `MaxEncodedLen`)
	/// Storage: `Proxy::Announcements` (r:1 w:1)
	/// Proof: `Proxy::Announcements` (`max_values`: None, `max_size`: Some(2233), added: 4708, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn proxy_announced(a: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `358 + a * (68 ±0) + p * (37 ±0)`
		//  Estimated: `5698`
		// Minimum execution time: 35_383_000 picoseconds.
		Weight::from_parts(35_294_835, 0)
			.saturating_add(Weight::from_parts(0, 5698))
			// Standard Error: 2_480
			.saturating_add(Weight::from_parts(173_465, 0).saturating_mul(a.into()))
			// Standard Error: 2_562
			.saturating_add(Weight::from_parts(44_355, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Proxy::Announcements` (r:1 w:1)
	/// Proof: `Proxy::Announcements` (`max_values`: None, `max_size`: Some(2233), added: 4708, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn remove_announcement(a: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `272 + a * (68 ±0)`
		//  Estimated: `5698`
		// Minimum execution time: 23_769_000 picoseconds.
		Weight::from_parts(24_647_230, 0)
			.saturating_add(Weight::from_parts(0, 5698))
			// Standard Error: 1_635
			.saturating_add(Weight::from_parts(161_251, 0).saturating_mul(a.into()))
			// Standard Error: 1_690
			.saturating_add(Weight::from_parts(13_924, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Proxy::Announcements` (r:1 w:1)
	/// Proof: `Proxy::Announcements` (`max_values`: None, `max_size`: Some(2233), added: 4708, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn reject_announcement(a: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `272 + a * (68 ±0)`
		//  Estimated: `5698`
		// Minimum execution time: 23_807_000 picoseconds.
		Weight::from_parts(24_792_990, 0)
			.saturating_add(Weight::from_parts(0, 5698))
			// Standard Error: 1_199
			.saturating_add(Weight::from_parts(162_525, 0).saturating_mul(a.into()))
			// Standard Error: 1_239
			.saturating_add(Weight::from_parts(4_511, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Proxy::Proxies` (r:1 w:0)
	/// Proof: `Proxy::Proxies` (`max_values`: None, `max_size`: Some(1241), added: 3716, mode: `MaxEncodedLen`)
	/// Storage: `Proxy::Announcements` (r:1 w:1)
	/// Proof: `Proxy::Announcements` (`max_values`: None, `max_size`: Some(2233), added: 4708, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn announce(a: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `290 + a * (68 ±0) + p * (37 ±0)`
		//  Estimated: `5698`
		// Minimum execution time: 31_786_000 picoseconds.
		Weight::from_parts(32_165_982, 0)
			.saturating_add(Weight::from_parts(0, 5698))
			// Standard Error: 2_985
			.saturating_add(Weight::from_parts(179_305, 0).saturating_mul(a.into()))
			// Standard Error: 3_084
			.saturating_add(Weight::from_parts(60_070, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Proxy::Proxies` (r:1 w:1)
	/// Proof: `Proxy::Proxies` (`max_values`: None, `max_size`: Some(1241), added: 3716, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[1, 31]`.
	fn add_proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `65 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 21_298_000 picoseconds.
		Weight::from_parts(22_168_228, 0)
			.saturating_add(Weight::from_parts(0, 4706))
			// Standard Error: 833
			.saturating_add(Weight::from_parts(46_188, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Proxy::Proxies` (r:1 w:1)
	/// Proof: `Proxy::Proxies` (`max_values`: None, `max_size`: Some(1241), added: 3716, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[1, 31]`.
	fn remove_proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `65 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 21_187_000 picoseconds.
		Weight::from_parts(22_059_229, 0)
			.saturating_add(Weight::from_parts(0, 4706))
			// Standard Error: 1_067
			.saturating_add(Weight::from_parts(61_963, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Proxy::Proxies` (r:1 w:1)
	/// Proof: `Proxy::Proxies` (`max_values`: None, `max_size`: Some(1241), added: 3716, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[1, 31]`.
	fn remove_proxies(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `65 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 18_835_000 picoseconds.
		Weight::from_parts(19_634_505, 0)
			.saturating_add(Weight::from_parts(0, 4706))
			// Standard Error: 805
			.saturating_add(Weight::from_parts(38_852, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Proxy::Proxies` (r:1 w:1)
	/// Proof: `Proxy::Proxies` (`max_values`: None, `max_size`: Some(1241), added: 3716, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[1, 31]`.
	fn create_pure(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76`
		//  Estimated: `4706`
		// Minimum execution time: 22_826_000 picoseconds.
		Weight::from_parts(23_660_768, 0)
			.saturating_add(Weight::from_parts(0, 4706))
			// Standard Error: 908
			.saturating_add(Weight::from_parts(13_921, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Proxy::Proxies` (r:1 w:1)
	/// Proof: `Proxy::Proxies` (`max_values`: None, `max_size`: Some(1241), added: 3716, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[0, 30]`.
	fn kill_pure(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `102 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 20_340_000 picoseconds.
		Weight::from_parts(21_367_529, 0)
			.saturating_add(Weight::from_parts(0, 4706))
			// Standard Error: 1_044
			.saturating_add(Weight::from_parts(38_256, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
