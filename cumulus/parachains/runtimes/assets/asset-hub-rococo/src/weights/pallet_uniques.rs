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

//! Autogenerated weights for `pallet_uniques`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-20, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `b2b492c97648`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("asset-hub-rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=asset-hub-rococo-dev
// --pallet=pallet_uniques
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/assets/asset-hub-rococo/src/weights
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

/// Weight functions for `pallet_uniques`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_uniques::WeightInfo for WeightInfo<T> {
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ClassAccount` (r:0 w:1)
	/// Proof: `Uniques::ClassAccount` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	fn create() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `179`
		//  Estimated: `3643`
		// Minimum execution time: 28_469_000 picoseconds.
		Weight::from_parts(29_174_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ClassAccount` (r:0 w:1)
	/// Proof: `Uniques::ClassAccount` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	fn force_create() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76`
		//  Estimated: `3643`
		// Minimum execution time: 12_902_000 picoseconds.
		Weight::from_parts(13_273_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Asset` (r:1001 w:1000)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::InstanceMetadataOf` (r:1000 w:1000)
	/// Proof: `Uniques::InstanceMetadataOf` (`max_values`: None, `max_size`: Some(187), added: 2662, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Attribute` (r:1000 w:1000)
	/// Proof: `Uniques::Attribute` (`max_values`: None, `max_size`: Some(172), added: 2647, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ClassAccount` (r:0 w:1)
	/// Proof: `Uniques::ClassAccount` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ClassMetadataOf` (r:0 w:1)
	/// Proof: `Uniques::ClassMetadataOf` (`max_values`: None, `max_size`: Some(167), added: 2642, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Account` (r:0 w:1000)
	/// Proof: `Uniques::Account` (`max_values`: None, `max_size`: Some(88), added: 2563, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::CollectionMaxSupply` (r:0 w:1)
	/// Proof: `Uniques::CollectionMaxSupply` (`max_values`: None, `max_size`: Some(24), added: 2499, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[0, 1000]`.
	/// The range of component `m` is `[0, 1000]`.
	/// The range of component `a` is `[0, 1000]`.
	fn destroy(n: u32, m: u32, a: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `327 + a * (107 ±0) + m * (56 ±0) + n * (76 ±0)`
		//  Estimated: `3643 + a * (2647 ±0) + m * (2662 ±0) + n * (2597 ±0)`
		// Minimum execution time: 3_165_320_000 picoseconds.
		Weight::from_parts(3_208_567_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			// Standard Error: 34_790
			.saturating_add(Weight::from_parts(8_076_032, 0).saturating_mul(n.into()))
			// Standard Error: 34_790
			.saturating_add(Weight::from_parts(380_636, 0).saturating_mul(m.into()))
			// Standard Error: 34_790
			.saturating_add(Weight::from_parts(465_800, 0).saturating_mul(a.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(n.into())))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(m.into())))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(a.into())))
			.saturating_add(T::DbWeight::get().writes(4))
			.saturating_add(T::DbWeight::get().writes((2_u64).saturating_mul(n.into())))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(m.into())))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(a.into())))
			.saturating_add(Weight::from_parts(0, 2647).saturating_mul(a.into()))
			.saturating_add(Weight::from_parts(0, 2662).saturating_mul(m.into()))
			.saturating_add(Weight::from_parts(0, 2597).saturating_mul(n.into()))
	}
	/// Storage: `Uniques::Asset` (r:1 w:1)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::CollectionMaxSupply` (r:1 w:0)
	/// Proof: `Uniques::CollectionMaxSupply` (`max_values`: None, `max_size`: Some(24), added: 2499, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Account` (r:0 w:1)
	/// Proof: `Uniques::Account` (`max_values`: None, `max_size`: Some(88), added: 2563, mode: `MaxEncodedLen`)
	fn mint() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `316`
		//  Estimated: `3643`
		// Minimum execution time: 35_874_000 picoseconds.
		Weight::from_parts(36_984_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Asset` (r:1 w:1)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Account` (r:0 w:1)
	/// Proof: `Uniques::Account` (`max_values`: None, `max_size`: Some(88), added: 2563, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ItemPriceOf` (r:0 w:1)
	/// Proof: `Uniques::ItemPriceOf` (`max_values`: None, `max_size`: Some(89), added: 2564, mode: `MaxEncodedLen`)
	fn burn() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462`
		//  Estimated: `3643`
		// Minimum execution time: 37_355_000 picoseconds.
		Weight::from_parts(38_467_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `Uniques::Class` (r:1 w:0)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Asset` (r:1 w:1)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Account` (r:0 w:2)
	/// Proof: `Uniques::Account` (`max_values`: None, `max_size`: Some(88), added: 2563, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ItemPriceOf` (r:0 w:1)
	/// Proof: `Uniques::ItemPriceOf` (`max_values`: None, `max_size`: Some(89), added: 2564, mode: `MaxEncodedLen`)
	fn transfer() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462`
		//  Estimated: `3643`
		// Minimum execution time: 27_646_000 picoseconds.
		Weight::from_parts(28_283_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Asset` (r:5000 w:5000)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// The range of component `i` is `[0, 5000]`.
	fn redeposit(i: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `772 + i * (76 ±0)`
		//  Estimated: `3643 + i * (2597 ±0)`
		// Minimum execution time: 13_135_000 picoseconds.
		Weight::from_parts(13_658_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			// Standard Error: 20_208
			.saturating_add(Weight::from_parts(18_009_451, 0).saturating_mul(i.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(i.into())))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(i.into())))
			.saturating_add(Weight::from_parts(0, 2597).saturating_mul(i.into()))
	}
	/// Storage: `Uniques::Asset` (r:1 w:1)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Class` (r:1 w:0)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	fn freeze() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462`
		//  Estimated: `3643`
		// Minimum execution time: 18_382_000 picoseconds.
		Weight::from_parts(19_322_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::Asset` (r:1 w:1)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Class` (r:1 w:0)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	fn thaw() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462`
		//  Estimated: `3643`
		// Minimum execution time: 18_825_000 picoseconds.
		Weight::from_parts(19_451_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	fn freeze_collection() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `316`
		//  Estimated: `3643`
		// Minimum execution time: 12_588_000 picoseconds.
		Weight::from_parts(12_956_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	fn thaw_collection() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `316`
		//  Estimated: `3643`
		// Minimum execution time: 12_346_000 picoseconds.
		Weight::from_parts(12_683_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::OwnershipAcceptance` (r:1 w:1)
	/// Proof: `Uniques::OwnershipAcceptance` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ClassAccount` (r:0 w:2)
	/// Proof: `Uniques::ClassAccount` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	fn transfer_ownership() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `493`
		//  Estimated: `3643`
		// Minimum execution time: 30_500_000 picoseconds.
		Weight::from_parts(31_641_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	fn set_team() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `316`
		//  Estimated: `3643`
		// Minimum execution time: 12_651_000 picoseconds.
		Weight::from_parts(13_185_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ClassAccount` (r:0 w:1)
	/// Proof: `Uniques::ClassAccount` (`max_values`: None, `max_size`: Some(68), added: 2543, mode: `MaxEncodedLen`)
	fn force_item_status() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `316`
		//  Estimated: `3643`
		// Minimum execution time: 15_868_000 picoseconds.
		Weight::from_parts(16_215_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::InstanceMetadataOf` (r:1 w:0)
	/// Proof: `Uniques::InstanceMetadataOf` (`max_values`: None, `max_size`: Some(187), added: 2662, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Attribute` (r:1 w:1)
	/// Proof: `Uniques::Attribute` (`max_values`: None, `max_size`: Some(172), added: 2647, mode: `MaxEncodedLen`)
	fn set_attribute() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `593`
		//  Estimated: `3652`
		// Minimum execution time: 40_460_000 picoseconds.
		Weight::from_parts(42_429_000, 0)
			.saturating_add(Weight::from_parts(0, 3652))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::InstanceMetadataOf` (r:1 w:0)
	/// Proof: `Uniques::InstanceMetadataOf` (`max_values`: None, `max_size`: Some(187), added: 2662, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Attribute` (r:1 w:1)
	/// Proof: `Uniques::Attribute` (`max_values`: None, `max_size`: Some(172), added: 2647, mode: `MaxEncodedLen`)
	fn clear_attribute() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `790`
		//  Estimated: `3652`
		// Minimum execution time: 43_324_000 picoseconds.
		Weight::from_parts(44_232_000, 0)
			.saturating_add(Weight::from_parts(0, 3652))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::InstanceMetadataOf` (r:1 w:1)
	/// Proof: `Uniques::InstanceMetadataOf` (`max_values`: None, `max_size`: Some(187), added: 2662, mode: `MaxEncodedLen`)
	fn set_metadata() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `382`
		//  Estimated: `3652`
		// Minimum execution time: 29_613_000 picoseconds.
		Weight::from_parts(30_617_000, 0)
			.saturating_add(Weight::from_parts(0, 3652))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::InstanceMetadataOf` (r:1 w:1)
	/// Proof: `Uniques::InstanceMetadataOf` (`max_values`: None, `max_size`: Some(187), added: 2662, mode: `MaxEncodedLen`)
	fn clear_metadata() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `593`
		//  Estimated: `3652`
		// Minimum execution time: 31_461_000 picoseconds.
		Weight::from_parts(32_334_000, 0)
			.saturating_add(Weight::from_parts(0, 3652))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ClassMetadataOf` (r:1 w:1)
	/// Proof: `Uniques::ClassMetadataOf` (`max_values`: None, `max_size`: Some(167), added: 2642, mode: `MaxEncodedLen`)
	fn set_collection_metadata() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `316`
		//  Estimated: `3643`
		// Minimum execution time: 30_290_000 picoseconds.
		Weight::from_parts(31_074_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:1)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ClassMetadataOf` (r:1 w:1)
	/// Proof: `Uniques::ClassMetadataOf` (`max_values`: None, `max_size`: Some(167), added: 2642, mode: `MaxEncodedLen`)
	fn clear_collection_metadata() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `507`
		//  Estimated: `3643`
		// Minimum execution time: 29_959_000 picoseconds.
		Weight::from_parts(30_679_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Uniques::Class` (r:1 w:0)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Asset` (r:1 w:1)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	fn approve_transfer() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462`
		//  Estimated: `3643`
		// Minimum execution time: 19_201_000 picoseconds.
		Weight::from_parts(19_701_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::Class` (r:1 w:0)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Asset` (r:1 w:1)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	fn cancel_approval() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `495`
		//  Estimated: `3643`
		// Minimum execution time: 18_935_000 picoseconds.
		Weight::from_parts(19_443_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::OwnershipAcceptance` (r:1 w:1)
	/// Proof: `Uniques::OwnershipAcceptance` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	fn set_accept_ownership() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `76`
		//  Estimated: `3517`
		// Minimum execution time: 13_704_000 picoseconds.
		Weight::from_parts(14_176_000, 0)
			.saturating_add(Weight::from_parts(0, 3517))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::CollectionMaxSupply` (r:1 w:1)
	/// Proof: `Uniques::CollectionMaxSupply` (`max_values`: None, `max_size`: Some(24), added: 2499, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Class` (r:1 w:0)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	fn set_collection_max_supply() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `316`
		//  Estimated: `3643`
		// Minimum execution time: 15_261_000 picoseconds.
		Weight::from_parts(15_820_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::Asset` (r:1 w:0)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ItemPriceOf` (r:0 w:1)
	/// Proof: `Uniques::ItemPriceOf` (`max_values`: None, `max_size`: Some(89), added: 2564, mode: `MaxEncodedLen`)
	fn set_price() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `293`
		//  Estimated: `3587`
		// Minimum execution time: 15_534_000 picoseconds.
		Weight::from_parts(15_958_000, 0)
			.saturating_add(Weight::from_parts(0, 3587))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Uniques::Asset` (r:1 w:1)
	/// Proof: `Uniques::Asset` (`max_values`: None, `max_size`: Some(122), added: 2597, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::ItemPriceOf` (r:1 w:1)
	/// Proof: `Uniques::ItemPriceOf` (`max_values`: None, `max_size`: Some(89), added: 2564, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Class` (r:1 w:0)
	/// Proof: `Uniques::Class` (`max_values`: None, `max_size`: Some(178), added: 2653, mode: `MaxEncodedLen`)
	/// Storage: `Uniques::Account` (r:0 w:2)
	/// Proof: `Uniques::Account` (`max_values`: None, `max_size`: Some(88), added: 2563, mode: `MaxEncodedLen`)
	fn buy_item() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `574`
		//  Estimated: `3643`
		// Minimum execution time: 39_544_000 picoseconds.
		Weight::from_parts(40_793_000, 0)
			.saturating_add(Weight::from_parts(0, 3643))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(4))
	}
}
