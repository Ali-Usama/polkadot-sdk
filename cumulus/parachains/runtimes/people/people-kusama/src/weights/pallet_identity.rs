// Copyright Parity Technologies (UK) Ltd.
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

//! Weights taken from latest Kusama Relay Chain. Need to rerun.

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(missing_docs)]

use frame_support::{traits::Get, weights::Weight};
use core::marker::PhantomData;

/// Weight functions for `pallet_identity`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_identity::WeightInfo for WeightInfo<T> {
	/// Storage: Identity Registrars (r:1 w:1)
	/// Proof: Identity Registrars (max_values: Some(1), max_size: Some(1141), added: 1636, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 19]`.
	fn add_registrar(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `32 + r * (57 ±0)`
		//  Estimated: `2626`
		// Minimum execution time: 11_854_000 picoseconds.
		Weight::from_parts(12_968_221, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 5_813
			.saturating_add(Weight::from_parts(102_873, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity IdentityOf (r:1 w:1)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `x` is `[0, 100]`.
	fn set_identity(r: u32, x: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `442 + r * (5 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 32_800_000 picoseconds.
		Weight::from_parts(28_706_621, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 12_190
			.saturating_add(Weight::from_parts(261_969, 0).saturating_mul(r.into()))
			// Standard Error: 2_378
			.saturating_add(Weight::from_parts(500_617, 0).saturating_mul(x.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity IdentityOf (r:1 w:0)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// Storage: Identity SubsOf (r:1 w:1)
	/// Proof: Identity SubsOf (max_values: None, max_size: Some(3258), added: 5733, mode: MaxEncodedLen)
	/// Storage: Identity SuperOf (r:100 w:100)
	/// Proof: Identity SuperOf (max_values: None, max_size: Some(114), added: 2589, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 100]`.
	fn set_subs_new(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `101`
		//  Estimated: `11003 + s * (2589 ±0)`
		// Minimum execution time: 8_815_000 picoseconds.
		Weight::from_parts(21_946_444, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 5_757
			.saturating_add(Weight::from_parts(3_241_262, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(s.into())))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
			.saturating_add(Weight::from_parts(0, 2589).saturating_mul(s.into()))
	}
	/// Storage: Identity IdentityOf (r:1 w:0)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// Storage: Identity SubsOf (r:1 w:1)
	/// Proof: Identity SubsOf (max_values: None, max_size: Some(3258), added: 5733, mode: MaxEncodedLen)
	/// Storage: Identity SuperOf (r:0 w:100)
	/// Proof: Identity SuperOf (max_values: None, max_size: Some(114), added: 2589, mode: MaxEncodedLen)
	/// The range of component `p` is `[0, 100]`.
	fn set_subs_old(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `194 + p * (32 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 8_892_000 picoseconds.
		Weight::from_parts(21_343_974, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 5_109
			.saturating_add(Weight::from_parts(1_410_415, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(p.into())))
	}
	/// Storage: Identity SubsOf (r:1 w:1)
	/// Proof: Identity SubsOf (max_values: None, max_size: Some(3258), added: 5733, mode: MaxEncodedLen)
	/// Storage: Identity IdentityOf (r:1 w:1)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// Storage: Identity SuperOf (r:0 w:100)
	/// Proof: Identity SuperOf (max_values: None, max_size: Some(114), added: 2589, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `s` is `[0, 100]`.
	/// The range of component `x` is `[0, 100]`.
	fn clear_identity(r: u32, s: u32, x: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `469 + r * (5 ±0) + s * (32 ±0) + x * (66 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 60_331_000 picoseconds.
		Weight::from_parts(29_115_598, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 21_877
			.saturating_add(Weight::from_parts(216_644, 0).saturating_mul(r.into()))
			// Standard Error: 4_272
			.saturating_add(Weight::from_parts(1_420_433, 0).saturating_mul(s.into()))
			// Standard Error: 4_272
			.saturating_add(Weight::from_parts(311_436, 0).saturating_mul(x.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(2))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
	}
	/// Storage: Identity Registrars (r:1 w:0)
	/// Proof: Identity Registrars (max_values: Some(1), max_size: Some(1141), added: 1636, mode: MaxEncodedLen)
	/// Storage: Identity IdentityOf (r:1 w:1)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `x` is `[0, 100]`.
	fn request_judgement(r: u32, x: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `367 + r * (57 ±0) + x * (66 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 33_470_000 picoseconds.
		Weight::from_parts(32_277_730, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 4_577
			.saturating_add(Weight::from_parts(121_062, 0).saturating_mul(r.into()))
			// Standard Error: 893
			.saturating_add(Weight::from_parts(496_715, 0).saturating_mul(x.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity IdentityOf (r:1 w:1)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `x` is `[0, 100]`.
	fn cancel_request(r: u32, x: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `398 + x * (66 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 29_626_000 picoseconds.
		Weight::from_parts(28_419_375, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 5_566
			.saturating_add(Weight::from_parts(143_337, 0).saturating_mul(r.into()))
			// Standard Error: 1_086
			.saturating_add(Weight::from_parts(487_332, 0).saturating_mul(x.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity Registrars (r:1 w:1)
	/// Proof: Identity Registrars (max_values: Some(1), max_size: Some(1141), added: 1636, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 19]`.
	fn set_fee(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `89 + r * (57 ±0)`
		//  Estimated: `2626`
		// Minimum execution time: 7_221_000 picoseconds.
		Weight::from_parts(7_708_979, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_516
			.saturating_add(Weight::from_parts(101_163, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity Registrars (r:1 w:1)
	/// Proof: Identity Registrars (max_values: Some(1), max_size: Some(1141), added: 1636, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 19]`.
	fn set_account_id(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `89 + r * (57 ±0)`
		//  Estimated: `2626`
		// Minimum execution time: 7_288_000 picoseconds.
		Weight::from_parts(7_757_754, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_365
			.saturating_add(Weight::from_parts(95_345, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity Registrars (r:1 w:1)
	/// Proof: Identity Registrars (max_values: Some(1), max_size: Some(1141), added: 1636, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 19]`.
	fn set_fields(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `89 + r * (57 ±0)`
		//  Estimated: `2626`
		// Minimum execution time: 7_204_000 picoseconds.
		Weight::from_parts(7_679_617, 0)
			.saturating_add(Weight::from_parts(0, 2626))
			// Standard Error: 1_358
			.saturating_add(Weight::from_parts(100_186, 0).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity Registrars (r:1 w:0)
	/// Proof: Identity Registrars (max_values: Some(1), max_size: Some(1141), added: 1636, mode: MaxEncodedLen)
	/// Storage: Identity IdentityOf (r:1 w:1)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 19]`.
	/// The range of component `x` is `[0, 100]`.
	fn provide_judgement(r: u32, x: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `445 + r * (57 ±0) + x * (66 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 23_125_000 picoseconds.
		Weight::from_parts(22_392_893, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 5_154
			.saturating_add(Weight::from_parts(121_813, 0).saturating_mul(r.into()))
			// Standard Error: 953
			.saturating_add(Weight::from_parts(806_355, 0).saturating_mul(x.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity SubsOf (r:1 w:1)
	/// Proof: Identity SubsOf (max_values: None, max_size: Some(3258), added: 5733, mode: MaxEncodedLen)
	/// Storage: Identity IdentityOf (r:1 w:1)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Identity SuperOf (r:0 w:100)
	/// Proof: Identity SuperOf (max_values: None, max_size: Some(114), added: 2589, mode: MaxEncodedLen)
	/// The range of component `r` is `[1, 20]`.
	/// The range of component `s` is `[0, 100]`.
	/// The range of component `x` is `[0, 100]`.
	fn kill_identity(r: u32, s: u32, x: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `676 + r * (5 ±0) + s * (32 ±0) + x * (66 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 76_226_000 picoseconds.
		Weight::from_parts(35_456_327, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 18_829
			.saturating_add(Weight::from_parts(615_512, 0).saturating_mul(r.into()))
			// Standard Error: 3_677
			.saturating_add(Weight::from_parts(1_462_016, 0).saturating_mul(s.into()))
			// Standard Error: 3_677
			.saturating_add(Weight::from_parts(328_050, 0).saturating_mul(x.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(s.into())))
	}
	/// Storage: Identity IdentityOf (r:1 w:0)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// Storage: Identity SuperOf (r:1 w:1)
	/// Proof: Identity SuperOf (max_values: None, max_size: Some(114), added: 2589, mode: MaxEncodedLen)
	/// Storage: Identity SubsOf (r:1 w:1)
	/// Proof: Identity SubsOf (max_values: None, max_size: Some(3258), added: 5733, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 99]`.
	fn add_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `475 + s * (36 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 29_381_000 picoseconds.
		Weight::from_parts(33_288_068, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 1_624
			.saturating_add(Weight::from_parts(120_173, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: Identity IdentityOf (r:1 w:0)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// Storage: Identity SuperOf (r:1 w:1)
	/// Proof: Identity SuperOf (max_values: None, max_size: Some(114), added: 2589, mode: MaxEncodedLen)
	/// The range of component `s` is `[1, 100]`.
	fn rename_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `591 + s * (3 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 12_418_000 picoseconds.
		Weight::from_parts(13_798_930, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 856
			.saturating_add(Weight::from_parts(43_306, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: Identity IdentityOf (r:1 w:0)
	/// Proof: Identity IdentityOf (max_values: None, max_size: Some(7538), added: 10013, mode: MaxEncodedLen)
	/// Storage: Identity SuperOf (r:1 w:1)
	/// Proof: Identity SuperOf (max_values: None, max_size: Some(114), added: 2589, mode: MaxEncodedLen)
	/// Storage: Identity SubsOf (r:1 w:1)
	/// Proof: Identity SubsOf (max_values: None, max_size: Some(3258), added: 5733, mode: MaxEncodedLen)
	/// The range of component `s` is `[1, 100]`.
	fn remove_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `638 + s * (35 ±0)`
		//  Estimated: `11003`
		// Minimum execution time: 33_242_000 picoseconds.
		Weight::from_parts(36_552_253, 0)
			.saturating_add(Weight::from_parts(0, 11003))
			// Standard Error: 2_385
			.saturating_add(Weight::from_parts(98_359, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	/// Storage: Identity SuperOf (r:1 w:1)
	/// Proof: Identity SuperOf (max_values: None, max_size: Some(114), added: 2589, mode: MaxEncodedLen)
	/// Storage: Identity SubsOf (r:1 w:1)
	/// Proof: Identity SubsOf (max_values: None, max_size: Some(3258), added: 5733, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:0)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 99]`.
	fn quit_sub(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `704 + s * (37 ±0)`
		//  Estimated: `6723`
		// Minimum execution time: 24_017_000 picoseconds.
		Weight::from_parts(27_149_414, 0)
			.saturating_add(Weight::from_parts(0, 6723))
			// Standard Error: 1_769
			.saturating_add(Weight::from_parts(79_539, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(2))
	}
}
