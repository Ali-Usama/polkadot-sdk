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

//! Autogenerated weights for `pallet_identity`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `edfc0fc6bacd`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("people-rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=people-rococo-dev
// --pallet=pallet_identity
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/people/people-rococo/src/weights
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

/// Weight functions for `pallet_identity`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_identity::WeightInfo for WeightInfo<T> {
	/// Storage: `Identity::Registrars` (r:1 w:1)
	/// Proof: `Identity::Registrars` (`max_values`: Some(1), `max_size`: Some(1141), added: 1636, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 19]`.
	fn add_registrar(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `32 + r * (57 ±0)`
		//  Estimated: `2626`
		// Minimum execution time: 9_666_000 picoseconds.
		Weight::from_parts(10_402_890, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_932
			.saturating_add(Weight::from_parts(103_565, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	fn set_identity(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `441 + r * (5 ±0)`
		//  Estimated: `4269`
		// Minimum execution time: 19_969_000 picoseconds.
		Weight::from_parts(21_242_357, 0)
			.saturating_add(Weight::from_parts(0, 4269))
			// Standard Error: 2_498
			.saturating_add(Weight::from_parts(127_563, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:100 w:100)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[0, 100]`.
	fn set_subs_new(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `101`
		//  Estimated: `6723 + s * (2589 ±0)`
		// Minimum execution time: 13_967_000 picoseconds.
		Weight::from_parts(26_594_132, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 7_279
			.saturating_add(Weight::from_parts(3_819_160, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(s.into())))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
			.saturating_add(Weight::from_parts(0, 2589).saturating_mul(s.into()))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:0 w:100)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[0, 100]`.
	fn set_subs_old(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `194 + p * (32 ±0)`
		//  Estimated: `6723`
		// Minimum execution time: 13_863_000 picoseconds.
		Weight::from_parts(28_388_870, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 4_177
			.saturating_add(Weight::from_parts(1_436_115, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(p.into())))
	}
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:0 w:100)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `s` is `[0, 100]`.
	fn clear_identity(r: u32, s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `533 + r * (5 ±0) + s * (32 ±0)`
		//  Estimated: `6723`
		// Minimum execution time: 31_128_000 picoseconds.
		Weight::from_parts(32_571_414, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 11_443
			.saturating_add(Weight::from_parts(143_304, 0).saturating_mul(r.into()))
			// Standard Error: 2_232
			.saturating_add(Weight::from_parts(1_451_032, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
	}
	/// Storage: `Identity::Registrars` (r:1 w:0)
	/// Proof: `Identity::Registrars` (`max_values`: Some(1), `max_size`: Some(1141), added: 1636, mode: `MaxEncodedLen`)
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	fn request_judgement(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `431 + r * (57 ±0)`
		//  Estimated: `4269`
		// Minimum execution time: 30_942_000 picoseconds.
		Weight::from_parts(32_384_190, 0)
			.saturating_add(Weight::from_parts(0, 4269))
			// Standard Error: 2_992
			.saturating_add(Weight::from_parts(147_231, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	fn cancel_request(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `462`
		//  Estimated: `4269`
		// Minimum execution time: 29_078_000 picoseconds.
		Weight::from_parts(30_021_675, 0)
			.saturating_add(Weight::from_parts(0, 4269))
			// Standard Error: 3_822
			.saturating_add(Weight::from_parts(111_146, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::Registrars` (r:1 w:1)
	/// Proof: `Identity::Registrars` (`max_values`: Some(1), `max_size`: Some(1141), added: 1636, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 19]`.
	fn set_fee(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `89 + r * (57 ±0)`
		//  Estimated: `2626`
		// Minimum execution time: 7_056_000 picoseconds.
		Weight::from_parts(7_626_618, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_300
			.saturating_add(Weight::from_parts(83_400, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::Registrars` (r:1 w:1)
	/// Proof: `Identity::Registrars` (`max_values`: Some(1), `max_size`: Some(1141), added: 1636, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 19]`.
	fn set_account_id(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `89 + r * (57 ±0)`
		//  Estimated: `2626`
		// Minimum execution time: 7_287_000 picoseconds.
		Weight::from_parts(7_705_697, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_488
			.saturating_add(Weight::from_parts(80_619, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::Registrars` (r:1 w:1)
	/// Proof: `Identity::Registrars` (`max_values`: Some(1), `max_size`: Some(1141), added: 1636, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 19]`.
	fn set_fields(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `89 + r * (57 ±0)`
		//  Estimated: `2626`
		// Minimum execution time: 7_259_000 picoseconds.
		Weight::from_parts(7_591_512, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_536
			.saturating_add(Weight::from_parts(79_228, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::Registrars` (r:1 w:0)
	/// Proof: `Identity::Registrars` (`max_values`: Some(1), `max_size`: Some(1141), added: 1636, mode: `MaxEncodedLen`)
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 19]`.
	fn provide_judgement(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `509 + r * (57 ±0)`
		//  Estimated: `4269`
		// Minimum execution time: 22_285_000 picoseconds.
		Weight::from_parts(23_267_035, 0)
			.saturating_add(Weight::from_parts(0, 4269))
			// Standard Error: 2_218
			.saturating_add(Weight::from_parts(137_695, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:2)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `PolkadotXcm::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `Identity::SuperOf` (r:0 w:100)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `s` is `[0, 100]`.
	fn kill_identity(r: u32, s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `809 + r * (5 ±0) + s * (32 ±0)`
		//  Estimated: `6723 + r * (6 ±0) + s * (32 ±0)`
		// Minimum execution time: 95_281_000 picoseconds.
		Weight::from_parts(102_657_306, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 24_980
			.saturating_add(Weight::from_parts(252_401, 0).saturating_mul(r.into()))
			// Standard Error: 4_874
			.saturating_add(Weight::from_parts(1_543_186, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().writes(4))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
			.saturating_add(Weight::from_parts(0, 6).saturating_mul(r.into()))
			.saturating_add(Weight::from_parts(0, 32).saturating_mul(s.into()))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:1 w:1)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[0, 99]`.
	fn add_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `475 + s * (36 ±0)`
		//  Estimated: `6723`
		// Minimum execution time: 29_293_000 picoseconds.
		Weight::from_parts(35_627_334, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 1_806
			.saturating_add(Weight::from_parts(104_286, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:1 w:1)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[1, 100]`.
	fn rename_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `591 + s * (3 ±0)`
		//  Estimated: `4269`
		// Minimum execution time: 18_780_000 picoseconds.
		Weight::from_parts(21_462_781, 0)
			.saturating_add(Weight::from_parts(0, 4269))
			// Standard Error: 851
			.saturating_add(Weight::from_parts(61_652, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:1 w:1)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[1, 100]`.
	fn remove_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `638 + s * (35 ±0)`
		//  Estimated: `6723`
		// Minimum execution time: 34_550_000 picoseconds.
		Weight::from_parts(41_703_589, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 1_964
			.saturating_add(Weight::from_parts(108_813, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Identity::SuperOf` (r:1 w:1)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:0)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[0, 99]`.
	fn quit_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `704 + s * (37 ±0)`
		//  Estimated: `6723`
		// Minimum execution time: 26_143_000 picoseconds.
		Weight::from_parts(32_400_272, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 1_829
			.saturating_add(Weight::from_parts(105_673, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Identity::AuthorityOf` (r:0 w:1)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	fn add_username_authority() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 6_840_000 picoseconds.
		Weight::from_parts(7_170_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::AuthorityOf` (r:1 w:1)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	fn remove_username_authority() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `79`
		//  Estimated: `3517`
		// Minimum execution time: 10_721_000 picoseconds.
		Weight::from_parts(11_108_000, 0)
			.saturating_add(Weight::from_parts(0, 3517))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::AuthorityOf` (r:1 w:1)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameInfoOf` (r:1 w:1)
	/// Proof: `Identity::UsernameInfoOf` (`max_values`: None, `max_size`: Some(98), added: 2573, mode: `MaxEncodedLen`)
	/// Storage: `Identity::PendingUsernames` (r:1 w:0)
	/// Proof: `Identity::PendingUsernames` (`max_values`: None, `max_size`: Some(102), added: 2577, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameOf` (r:1 w:1)
	/// Proof: `Identity::UsernameOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[0, 1]`.
	fn set_username_for(_p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `182`
		//  Estimated: `3593`
		// Minimum execution time: 69_179_000 picoseconds.
		Weight::from_parts(87_598_808, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `Identity::PendingUsernames` (r:1 w:1)
	/// Proof: `Identity::PendingUsernames` (`max_values`: None, `max_size`: Some(102), added: 2577, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameOf` (r:1 w:1)
	/// Proof: `Identity::UsernameOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameInfoOf` (r:0 w:1)
	/// Proof: `Identity::UsernameInfoOf` (`max_values`: None, `max_size`: Some(98), added: 2573, mode: `MaxEncodedLen`)
	fn accept_username() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `116`
		//  Estimated: `3567`
		// Minimum execution time: 21_645_000 picoseconds.
		Weight::from_parts(22_464_000, 0)
			.saturating_add(Weight::from_parts(0, 3567))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Identity::PendingUsernames` (r:1 w:1)
	/// Proof: `Identity::PendingUsernames` (`max_values`: None, `max_size`: Some(102), added: 2577, mode: `MaxEncodedLen`)
	/// Storage: `Identity::AuthorityOf` (r:1 w:0)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[0, 1]`.
	fn remove_expired_approval(_p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `310`
		//  Estimated: `3593`
		// Minimum execution time: 16_538_000 picoseconds.
		Weight::from_parts(43_132_418, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Identity::UsernameInfoOf` (r:1 w:0)
	/// Proof: `Identity::UsernameInfoOf` (`max_values`: None, `max_size`: Some(98), added: 2573, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameOf` (r:0 w:1)
	/// Proof: `Identity::UsernameOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	fn set_primary_username() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `172`
		//  Estimated: `3563`
		// Minimum execution time: 13_980_000 picoseconds.
		Weight::from_parts(14_567_000, 0)
			.saturating_add(Weight::from_parts(0, 3563))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::UsernameInfoOf` (r:1 w:0)
	/// Proof: `Identity::UsernameInfoOf` (`max_values`: None, `max_size`: Some(98), added: 2573, mode: `MaxEncodedLen`)
	/// Storage: `Identity::AuthorityOf` (r:1 w:0)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UnbindingUsernames` (r:1 w:1)
	/// Proof: `Identity::UnbindingUsernames` (`max_values`: None, `max_size`: Some(53), added: 2528, mode: `MaxEncodedLen`)
	fn unbind_username() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `236`
		//  Estimated: `3563`
		// Minimum execution time: 19_377_000 picoseconds.
		Weight::from_parts(19_814_000, 0)
			.saturating_add(Weight::from_parts(0, 3563))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::UnbindingUsernames` (r:1 w:1)
	/// Proof: `Identity::UnbindingUsernames` (`max_values`: None, `max_size`: Some(53), added: 2528, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameInfoOf` (r:1 w:1)
	/// Proof: `Identity::UsernameInfoOf` (`max_values`: None, `max_size`: Some(98), added: 2573, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameOf` (r:1 w:1)
	/// Proof: `Identity::UsernameOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `Identity::AuthorityOf` (r:1 w:0)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	fn remove_username() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `297`
		//  Estimated: `3563`
		// Minimum execution time: 24_123_000 picoseconds.
		Weight::from_parts(24_653_000, 0)
			.saturating_add(Weight::from_parts(0, 3563))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `Identity::UsernameInfoOf` (r:1 w:1)
	/// Proof: `Identity::UsernameInfoOf` (`max_values`: None, `max_size`: Some(98), added: 2573, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameOf` (r:1 w:1)
	/// Proof: `Identity::UsernameOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UnbindingUsernames` (r:1 w:1)
	/// Proof: `Identity::UnbindingUsernames` (`max_values`: None, `max_size`: Some(53), added: 2528, mode: `MaxEncodedLen`)
	/// Storage: `Identity::AuthorityOf` (r:1 w:0)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:2 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::ShouldRecordXcm` (r:1 w:0)
	/// Proof: `PolkadotXcm::ShouldRecordXcm` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `p` is `[0, 1]`.
	fn kill_username(_p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `540`
		//  Estimated: `6196`
		// Minimum execution time: 22_295_000 picoseconds.
		Weight::from_parts(91_138_565, 0)
			.saturating_add(Weight::from_parts(0, 6196))
			.saturating_add(T::DbWeight::get().reads(8))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: UNKNOWN KEY `0x2aeddc77fe58c98d50bd37f1b90840f99622d1423cdd16f5c33e2b531c34a53d` (r:2 w:0)
	/// Proof: UNKNOWN KEY `0x2aeddc77fe58c98d50bd37f1b90840f99622d1423cdd16f5c33e2b531c34a53d` (r:2 w:0)
	/// Storage: `Identity::AuthorityOf` (r:0 w:1)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	fn migration_v2_authority_step() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `147`
		//  Estimated: `6087`
		// Minimum execution time: 9_198_000 picoseconds.
		Weight::from_parts(9_539_000, 0)
			.saturating_add(Weight::from_parts(0, 6087))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: UNKNOWN KEY `0x2aeddc77fe58c98d50bd37f1b90840f97c182fead9255863460affdd63116be3` (r:2 w:0)
	/// Proof: UNKNOWN KEY `0x2aeddc77fe58c98d50bd37f1b90840f97c182fead9255863460affdd63116be3` (r:2 w:0)
	/// Storage: `Identity::UsernameInfoOf` (r:0 w:1)
	/// Proof: `Identity::UsernameInfoOf` (`max_values`: None, `max_size`: Some(98), added: 2573, mode: `MaxEncodedLen`)
	fn migration_v2_username_step() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `159`
		//  Estimated: `6099`
		// Minimum execution time: 8_913_000 picoseconds.
		Weight::from_parts(9_546_000, 0)
			.saturating_add(Weight::from_parts(0, 6099))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:2 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(804), added: 3279, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameOf` (r:0 w:1)
	/// Proof: `Identity::UsernameOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	fn migration_v2_identity_step() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `526`
		//  Estimated: `7548`
		// Minimum execution time: 14_243_000 picoseconds.
		Weight::from_parts(14_702_000, 0)
			.saturating_add(Weight::from_parts(0, 7548))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Identity::PendingUsernames` (r:2 w:1)
	/// Proof: `Identity::PendingUsernames` (`max_values`: None, `max_size`: Some(102), added: 2577, mode: `MaxEncodedLen`)
	fn migration_v2_pending_username_step() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `201`
		//  Estimated: `6144`
		// Minimum execution time: 8_575_000 picoseconds.
		Weight::from_parts(9_159_000, 0)
			.saturating_add(Weight::from_parts(0, 6144))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::AuthorityOf` (r:2 w:0)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x2aeddc77fe58c98d50bd37f1b90840f99622d1423cdd16f5c33e2b531c34a53d` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0x2aeddc77fe58c98d50bd37f1b90840f99622d1423cdd16f5c33e2b531c34a53d` (r:1 w:1)
	fn migration_v2_cleanup_authority_step() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `288`
		//  Estimated: `6044`
		// Minimum execution time: 12_231_000 picoseconds.
		Weight::from_parts(13_182_000, 0)
			.saturating_add(Weight::from_parts(0, 6044))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::UsernameInfoOf` (r:2 w:0)
	/// Proof: `Identity::UsernameInfoOf` (`max_values`: None, `max_size`: Some(98), added: 2573, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x2aeddc77fe58c98d50bd37f1b90840f97c182fead9255863460affdd63116be3` (r:1 w:1)
	/// Proof: UNKNOWN KEY `0x2aeddc77fe58c98d50bd37f1b90840f97c182fead9255863460affdd63116be3` (r:1 w:1)
	fn migration_v2_cleanup_username_step() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `290`
		//  Estimated: `6136`
		// Minimum execution time: 11_731_000 picoseconds.
		Weight::from_parts(12_258_000, 0)
			.saturating_add(Weight::from_parts(0, 6136))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
