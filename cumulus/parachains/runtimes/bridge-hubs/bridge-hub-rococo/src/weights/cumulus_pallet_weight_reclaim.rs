// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Cumulus.
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

//! Autogenerated weights for `cumulus_pallet_weight_reclaim`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2024-12-30, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-ys-ssygq-project-674-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("bridge-hub-rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --steps=50
// --repeat=20
// --extrinsic=*
// --wasm-execution=compiled
// --heap-pages=4096
// --json-file=/builds/parity/mirrors/polkadot-sdk/.git/.artifacts/bench.json
// --pallet=cumulus_pallet_weight_reclaim
// --chain=bridge-hub-rococo-dev
// --header=./cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/bridge-hubs/bridge-hub-rococo/src/weights/

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::Weight};
use core::marker::PhantomData;

/// Weight functions for `cumulus_pallet_weight_reclaim`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> cumulus_pallet_weight_reclaim::WeightInfo for WeightInfo<T> {
	/// Storage: `System::BlockWeight` (r:1 w:1)
	/// Proof: `System::BlockWeight` (`max_values`: Some(1), `max_size`: Some(48), added: 543, mode: `MaxEncodedLen`)
	/// Storage: `System::ExtrinsicWeightReclaimed` (r:1 w:1)
	/// Proof: `System::ExtrinsicWeightReclaimed` (`max_values`: Some(1), `max_size`: Some(16), added: 511, mode: `MaxEncodedLen`)
	/// Storage: `System::AllExtrinsicsLen` (r:1 w:0)
	/// Proof: `System::AllExtrinsicsLen` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn storage_weight_reclaim() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `24`
		//  Estimated: `1533`
		// Minimum execution time: 6_988_000 picoseconds.
		Weight::from_parts(7_361_000, 0)
			.saturating_add(Weight::from_parts(0, 1533))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
}
