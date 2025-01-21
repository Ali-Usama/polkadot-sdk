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

//! Autogenerated weights for `pallet_identity`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `281d1f3fe473`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot
// benchmark
// pallet
// --extrinsic=*
// --chain=westend-dev
// --pallet=pallet_identity
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
		// Minimum execution time: 13_488_000 picoseconds.
		Weight::from_parts(14_099_021, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 2_263
			.saturating_add(Weight::from_parts(105_820, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	fn set_identity(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6977 + r * (5 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 117_876_000 picoseconds.
		Weight::from_parts(121_854_817, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 13_430
			.saturating_add(Weight::from_parts(133_293, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:100 w:100)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[0, 100]`.
	fn set_subs_new(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `101`
		//  Estimated: `11003 + s * (2589 ±0)`
		// Minimum execution time: 17_682_000 picoseconds.
		Weight::from_parts(31_885_612, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 6_641
			.saturating_add(Weight::from_parts(3_609_455, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(s.into())))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
			.saturating_add(Weight::from_parts(0, 2589).saturating_mul(s.into()))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:0 w:100)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[0, 100]`.
	fn set_subs_old(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `194 + p * (32 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 18_158_000 picoseconds.
		Weight::from_parts(31_962_751, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 3_767
			.saturating_add(Weight::from_parts(1_396_524, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(p.into())))
	}
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:0 w:100)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `s` is `[0, 100]`.
	fn clear_identity(r: u32, s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7069 + r * (5 ±0) + s * (32 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 65_036_000 picoseconds.
		Weight::from_parts(65_229_996, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 17_418
			.saturating_add(Weight::from_parts(271_417, 0).saturating_mul(r.into()))
			// Standard Error: 3_398
			.saturating_add(Weight::from_parts(1_405_517, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
	}
	/// Storage: `Identity::Registrars` (r:1 w:0)
	/// Proof: `Identity::Registrars` (`max_values`: Some(1), `max_size`: Some(1141), added: 1636, mode: `MaxEncodedLen`)
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	fn request_judgement(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6967 + r * (57 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 84_784_000 picoseconds.
		Weight::from_parts(86_558_058, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 8_983
			.saturating_add(Weight::from_parts(179_453, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	fn cancel_request(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6998`
		//  Estimated: `11003`
		// Minimum execution time: 84_400_000 picoseconds.
		Weight::from_parts(85_732_764, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 5_585
			.saturating_add(Weight::from_parts(199_199, 0).saturating_mul(r.into()))
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
		// Minimum execution time: 10_431_000 picoseconds.
		Weight::from_parts(11_099_401, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_840
			.saturating_add(Weight::from_parts(89_393, 0).saturating_mul(r.into()))
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
		// Minimum execution time: 10_577_000 picoseconds.
		Weight::from_parts(11_192_319, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 2_022
			.saturating_add(Weight::from_parts(77_817, 0).saturating_mul(r.into()))
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
		// Minimum execution time: 10_441_000 picoseconds.
		Weight::from_parts(11_104_557, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_708
			.saturating_add(Weight::from_parts(85_203, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::Registrars` (r:1 w:0)
	/// Proof: `Identity::Registrars` (`max_values`: Some(1), `max_size`: Some(1141), added: 1636, mode: `MaxEncodedLen`)
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 19]`.
	fn provide_judgement(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7045 + r * (57 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 104_458_000 picoseconds.
		Weight::from_parts(106_755_836, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 6_918
			.saturating_add(Weight::from_parts(106_046, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// Storage: `Identity::IdentityOf` (r:1 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:0 w:100)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `s` is `[0, 100]`.
	fn kill_identity(r: u32, s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7276 + r * (5 ±0) + s * (32 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 73_681_000 picoseconds.
		Weight::from_parts(71_931_166, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 21_498
			.saturating_add(Weight::from_parts(413_311, 0).saturating_mul(r.into()))
			// Standard Error: 4_194
			.saturating_add(Weight::from_parts(1_417_809, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:1 w:1)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[0, 99]`.
	fn add_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `475 + s * (36 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 33_015_000 picoseconds.
		Weight::from_parts(39_380_280, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 1_641
			.saturating_add(Weight::from_parts(107_480, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:1 w:1)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[1, 100]`.
	fn rename_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `591 + s * (3 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 22_118_000 picoseconds.
		Weight::from_parts(25_618_836, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 1_178
			.saturating_add(Weight::from_parts(57_882, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:1 w:0)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SuperOf` (r:1 w:1)
	/// Proof: `Identity::SuperOf` (`max_values`: None, `max_size`: Some(114), added: 2589, mode: `MaxEncodedLen`)
	/// Storage: `Identity::SubsOf` (r:1 w:1)
	/// Proof: `Identity::SubsOf` (`max_values`: None, `max_size`: Some(3258), added: 5733, mode: `MaxEncodedLen`)
	/// The range of component `s` is `[1, 100]`.
	fn remove_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `638 + s * (35 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 38_157_000 picoseconds.
		Weight::from_parts(42_108_939, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 1_367
			.saturating_add(Weight::from_parts(89_276, 0).saturating_mul(s.into()))
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
		// Minimum execution time: 29_152_000 picoseconds.
		Weight::from_parts(32_341_783, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 1_826
			.saturating_add(Weight::from_parts(102_255, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Identity::AuthorityOf` (r:0 w:1)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	fn add_username_authority() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 7_139_000 picoseconds.
		Weight::from_parts(7_606_000, 0)
			.saturating_add(Weight::from_parts(0, 0))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::AuthorityOf` (r:1 w:1)
	/// Proof: `Identity::AuthorityOf` (`max_values`: None, `max_size`: Some(52), added: 2527, mode: `MaxEncodedLen`)
	fn remove_username_authority() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `79`
		//  Estimated: `3517`
		// Minimum execution time: 14_502_000 picoseconds.
		Weight::from_parts(15_001_000, 0)
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
		//  Measured:  `219`
		//  Estimated: `3593`
		// Minimum execution time: 73_482_000 picoseconds.
		Weight::from_parts(94_338_083, 0)
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
		// Minimum execution time: 25_194_000 picoseconds.
		Weight::from_parts(26_220_000, 0)
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
		//  Measured:  `347`
		//  Estimated: `3593`
		// Minimum execution time: 25_974_000 picoseconds.
		Weight::from_parts(63_145_316, 0)
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
		// Minimum execution time: 18_045_000 picoseconds.
		Weight::from_parts(18_808_000, 0)
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
		// Minimum execution time: 22_914_000 picoseconds.
		Weight::from_parts(23_777_000, 0)
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
		// Minimum execution time: 27_659_000 picoseconds.
		Weight::from_parts(28_816_000, 0)
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
	/// Storage: `System::Account` (r:1 w:1)
	/// Proof: `System::Account` (`max_values`: None, `max_size`: Some(128), added: 2603, mode: `MaxEncodedLen`)
	/// The range of component `p` is `[0, 1]`.
	fn kill_username(_p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `508`
		//  Estimated: `3593`
		// Minimum execution time: 25_248_000 picoseconds.
		Weight::from_parts(49_296_995, 0)
			.saturating_add(Weight::from_parts(0, 3593))
			.saturating_add(T::DbWeight::get().reads(5))
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
		// Minimum execution time: 9_151_000 picoseconds.
		Weight::from_parts(9_632_000, 0)
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
		// Minimum execution time: 9_342_000 picoseconds.
		Weight::from_parts(9_668_000, 0)
			.saturating_add(Weight::from_parts(0, 6099))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `Identity::IdentityOf` (r:2 w:1)
	/// Proof: `Identity::IdentityOf` (`max_values`: None, `max_size`: Some(7538), added: 10013, mode: `MaxEncodedLen`)
	/// Storage: `Identity::UsernameOf` (r:0 w:1)
	/// Proof: `Identity::UsernameOf` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	fn migration_v2_identity_step() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `7062`
		//  Estimated: `21016`
		// Minimum execution time: 69_726_000 picoseconds.
		Weight::from_parts(70_620_000, 0)
			.saturating_add(Weight::from_parts(0, 21016))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: `Identity::PendingUsernames` (r:2 w:1)
	/// Proof: `Identity::PendingUsernames` (`max_values`: None, `max_size`: Some(102), added: 2577, mode: `MaxEncodedLen`)
	fn migration_v2_pending_username_step() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `201`
		//  Estimated: `6144`
		// Minimum execution time: 11_721_000 picoseconds.
		Weight::from_parts(12_025_000, 0)
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
		// Minimum execution time: 15_930_000 picoseconds.
		Weight::from_parts(16_537_000, 0)
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
		// Minimum execution time: 14_783_000 picoseconds.
		Weight::from_parts(15_175_000, 0)
			.saturating_add(Weight::from_parts(0, 6136))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(1))
	}
}
