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

//! Autogenerated weights for `snowbridge_pallet_ethereum_client`
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
// --pallet=snowbridge_pallet_ethereum_client
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

/// Weight functions for `snowbridge_pallet_ethereum_client`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> snowbridge_pallet_ethereum_client::WeightInfo for WeightInfo<T> {
	/// Storage: `EthereumBeaconClient::FinalizedBeaconStateIndex` (r:1 w:1)
	/// Proof: `EthereumBeaconClient::FinalizedBeaconStateIndex` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::FinalizedBeaconStateMapping` (r:1 w:1)
	/// Proof: `EthereumBeaconClient::FinalizedBeaconStateMapping` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::NextSyncCommittee` (r:0 w:1)
	/// Proof: `EthereumBeaconClient::NextSyncCommittee` (`max_values`: Some(1), `max_size`: Some(92372), added: 92867, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::InitialCheckpointRoot` (r:0 w:1)
	/// Proof: `EthereumBeaconClient::InitialCheckpointRoot` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::ValidatorsRoot` (r:0 w:1)
	/// Proof: `EthereumBeaconClient::ValidatorsRoot` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::LatestFinalizedBlockRoot` (r:0 w:1)
	/// Proof: `EthereumBeaconClient::LatestFinalizedBlockRoot` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::CurrentSyncCommittee` (r:0 w:1)
	/// Proof: `EthereumBeaconClient::CurrentSyncCommittee` (`max_values`: Some(1), `max_size`: Some(92372), added: 92867, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::FinalizedBeaconState` (r:0 w:1)
	/// Proof: `EthereumBeaconClient::FinalizedBeaconState` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	fn force_checkpoint() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76`
		//  Estimated: `3501`
		// Minimum execution time: 102_325_888_000 picoseconds.
		Weight::from_parts(102_439_892_000, 0)
			.saturating_add(Weight::from_parts(0, 3501))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(8))
	}
	/// Storage: `EthereumBeaconClient::OperatingMode` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::OperatingMode` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::LatestFinalizedBlockRoot` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::LatestFinalizedBlockRoot` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::FinalizedBeaconState` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::FinalizedBeaconState` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::NextSyncCommittee` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::NextSyncCommittee` (`max_values`: Some(1), `max_size`: Some(92372), added: 92867, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::CurrentSyncCommittee` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::CurrentSyncCommittee` (`max_values`: Some(1), `max_size`: Some(92372), added: 92867, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::ValidatorsRoot` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::ValidatorsRoot` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::LatestSyncCommitteeUpdatePeriod` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::LatestSyncCommitteeUpdatePeriod` (`max_values`: Some(1), `max_size`: Some(8), added: 503, mode: `MaxEncodedLen`)
	fn submit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `92772`
		//  Estimated: `93857`
		// Minimum execution time: 25_897_272_000 picoseconds.
		Weight::from_parts(25_933_085_000, 0)
			.saturating_add(Weight::from_parts(0, 93857))
			.saturating_add(T::DbWeight::get().reads(7))
	}
	/// Storage: `EthereumBeaconClient::OperatingMode` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::OperatingMode` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::LatestFinalizedBlockRoot` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::LatestFinalizedBlockRoot` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::FinalizedBeaconState` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::FinalizedBeaconState` (`max_values`: None, `max_size`: Some(72), added: 2547, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::NextSyncCommittee` (r:1 w:1)
	/// Proof: `EthereumBeaconClient::NextSyncCommittee` (`max_values`: Some(1), `max_size`: Some(92372), added: 92867, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::CurrentSyncCommittee` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::CurrentSyncCommittee` (`max_values`: Some(1), `max_size`: Some(92372), added: 92867, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::ValidatorsRoot` (r:1 w:0)
	/// Proof: `EthereumBeaconClient::ValidatorsRoot` (`max_values`: Some(1), `max_size`: Some(32), added: 527, mode: `MaxEncodedLen`)
	/// Storage: `EthereumBeaconClient::LatestSyncCommitteeUpdatePeriod` (r:1 w:1)
	/// Proof: `EthereumBeaconClient::LatestSyncCommitteeUpdatePeriod` (`max_values`: Some(1), `max_size`: Some(8), added: 503, mode: `MaxEncodedLen`)
	fn submit_with_sync_committee() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `92772`
		//  Estimated: `93857`
		// Minimum execution time: 128_241_936_000 picoseconds.
		Weight::from_parts(128_342_171_000, 0)
			.saturating_add(Weight::from_parts(0, 93857))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(2))
	}
}
