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

//! Autogenerated weights for `frame_system_extensions`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-02-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `3c79cbcee5bb`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `None`, DB CACHE: 1024

// Executed Command:
// frame-omni-bencher
// v1
// benchmark
// pallet
// --extrinsic=*
// --runtime=target/production/wbuild/asset-hub-westend-runtime/asset_hub_westend_runtime.wasm
// --pallet=frame_system_extensions
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

/// Weight functions for `frame_system_extensions`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> frame_system::ExtensionsWeightInfo for WeightInfo<T> {
	fn check_genesis() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `30`
		//  Estimated: `0`
		// Minimum execution time: 3_288_000 picoseconds.
		Weight::from_parts(3_400_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	fn check_mortality_mortal_transaction() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `68`
		//  Estimated: `0`
		// Minimum execution time: 6_504_000 picoseconds.
		Weight::from_parts(6_667_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	fn check_mortality_immortal_transaction() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `68`
		//  Estimated: `0`
		// Minimum execution time: 6_432_000 picoseconds.
		Weight::from_parts(6_641_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	fn check_non_zero_sender() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 563_000 picoseconds.
		Weight::from_parts(617_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	fn check_nonce() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `101`
		//  Estimated: `3593`
		// Minimum execution time: 6_776_000 picoseconds.
		Weight::from_parts(7_102_000, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	fn check_spec_version() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 395_000 picoseconds.
		Weight::from_parts(455_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	fn check_tx_version() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 402_000 picoseconds.
		Weight::from_parts(446_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	fn check_weight() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 3_787_000 picoseconds.
		Weight::from_parts(4_062_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
	fn weight_reclaim() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_215_000 picoseconds.
		Weight::from_parts(2_407_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
	}
}
