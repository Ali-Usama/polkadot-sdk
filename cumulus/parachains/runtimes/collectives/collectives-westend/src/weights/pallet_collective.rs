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

//! Autogenerated weights for `pallet_collective`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-21, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `2ef552afe55a`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("collectives-westend-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=collectives-westend-dev
// --pallet=pallet_collective
// --header=/__w/polkadot-sdk/polkadot-sdk/cumulus/file_header.txt
// --output=./cumulus/parachains/runtimes/collectives/collectives-westend/src/weights
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

/// Weight functions for `pallet_collective`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_collective::WeightInfo for WeightInfo<T> {
	/// Storage: `AllianceMotion::Members` (r:1 w:1)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Proposals` (r:1 w:0)
	/// Proof: `AllianceMotion::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Voting` (r:100 w:100)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Prime` (r:0 w:1)
	/// Proof: `AllianceMotion::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[0, 100]`.
	/// The range of component `n` is `[0, 100]`.
	/// The range of component `p` is `[0, 100]`.
	fn set_members(m: u32, _n: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0 + m * (3232 ±0) + p * (3190 ±0)`
		//  Estimated: `15728 + m * (1967 ±23) + p * (4332 ±23)`
		// Minimum execution time: 16_645_000 picoseconds.
		Weight::from_parts(16_803_000, 0)
			.saturating_add(Weight::from_parts(0, 15728))
			// Standard Error: 61_765
			.saturating_add(Weight::from_parts(4_657_469, 0).saturating_mul(m.into()))
			// Standard Error: 61_765
			.saturating_add(Weight::from_parts(9_114_335, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(p.into())))
			.saturating_add(T::DbWeight::get().writes(2))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(p.into())))
			.saturating_add(Weight::from_parts(0, 1967).saturating_mul(m.into()))
			.saturating_add(Weight::from_parts(0, 4332).saturating_mul(p.into()))
	}
	/// Storage: `AllianceMotion::Members` (r:1 w:0)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `b` is `[2, 1024]`.
	/// The range of component `m` is `[1, 100]`.
	fn execute(b: u32, m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `69 + m * (32 ±0)`
		//  Estimated: `1555 + m * (32 ±0)`
		// Minimum execution time: 14_950_000 picoseconds.
		Weight::from_parts(14_092_124, 0)
			.saturating_add(Weight::from_parts(0, 1555))
			// Standard Error: 23
			.saturating_add(Weight::from_parts(1_449, 0).saturating_mul(b.into()))
			// Standard Error: 238
			.saturating_add(Weight::from_parts(14_645, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(Weight::from_parts(0, 32).saturating_mul(m.into()))
	}
	/// Storage: `AllianceMotion::Members` (r:1 w:0)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::ProposalOf` (r:1 w:0)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `b` is `[2, 1024]`.
	/// The range of component `m` is `[1, 100]`.
	fn propose_execute(b: u32, m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `69 + m * (32 ±0)`
		//  Estimated: `3535 + m * (32 ±0)`
		// Minimum execution time: 17_889_000 picoseconds.
		Weight::from_parts(16_837_350, 0)
			.saturating_add(Weight::from_parts(0, 3535))
			// Standard Error: 35
			.saturating_add(Weight::from_parts(1_524, 0).saturating_mul(b.into()))
			// Standard Error: 361
			.saturating_add(Weight::from_parts(23_598, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(Weight::from_parts(0, 32).saturating_mul(m.into()))
	}
	/// Storage: `AllianceMotion::Members` (r:1 w:0)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::ProposalOf` (r:1 w:1)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Proposals` (r:1 w:1)
	/// Proof: `AllianceMotion::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::ProposalCount` (r:1 w:1)
	/// Proof: `AllianceMotion::ProposalCount` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Voting` (r:0 w:1)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `b` is `[2, 1024]`.
	/// The range of component `m` is `[2, 100]`.
	/// The range of component `p` is `[1, 100]`.
	fn propose_proposed(b: u32, m: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `359 + m * (32 ±0) + p * (36 ±0)`
		//  Estimated: `3751 + m * (33 ±0) + p * (36 ±0)`
		// Minimum execution time: 23_516_000 picoseconds.
		Weight::from_parts(23_494_040, 0)
			.saturating_add(Weight::from_parts(0, 3751))
			// Standard Error: 242
			.saturating_add(Weight::from_parts(2_560, 0).saturating_mul(b.into()))
			// Standard Error: 2_534
			.saturating_add(Weight::from_parts(41_717, 0).saturating_mul(m.into()))
			// Standard Error: 2_502
			.saturating_add(Weight::from_parts(205_684, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(4))
			.saturating_add(Weight::from_parts(0, 33).saturating_mul(m.into()))
			.saturating_add(Weight::from_parts(0, 36).saturating_mul(p.into()))
	}
	/// Storage: `AllianceMotion::Members` (r:1 w:0)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Voting` (r:1 w:1)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[5, 100]`.
	fn vote(m: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `808 + m * (64 ±0)`
		//  Estimated: `4272 + m * (64 ±0)`
		// Minimum execution time: 32_037_000 picoseconds.
		Weight::from_parts(32_929_271, 0)
			.saturating_add(Weight::from_parts(0, 4272))
			// Standard Error: 929
			.saturating_add(Weight::from_parts(43_694, 0).saturating_mul(m.into()))
			.saturating_add(T::DbWeight::get().reads(2))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(Weight::from_parts(0, 64).saturating_mul(m.into()))
	}
	/// Storage: `AllianceMotion::Voting` (r:1 w:1)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Members` (r:1 w:0)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Proposals` (r:1 w:1)
	/// Proof: `AllianceMotion::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::ProposalOf` (r:0 w:1)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[4, 100]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_early_disapproved(m: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `397 + m * (64 ±0) + p * (36 ±0)`
		//  Estimated: `3842 + m * (65 ±0) + p * (36 ±0)`
		// Minimum execution time: 26_529_000 picoseconds.
		Weight::from_parts(30_800_465, 0)
			.saturating_add(Weight::from_parts(0, 3842))
			// Standard Error: 1_656
			.saturating_add(Weight::from_parts(35_162, 0).saturating_mul(m.into()))
			// Standard Error: 1_615
			.saturating_add(Weight::from_parts(204_856, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(Weight::from_parts(0, 65).saturating_mul(m.into()))
			.saturating_add(Weight::from_parts(0, 36).saturating_mul(p.into()))
	}
	/// Storage: `AllianceMotion::Voting` (r:1 w:1)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Members` (r:1 w:0)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::ProposalOf` (r:1 w:1)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Proposals` (r:1 w:1)
	/// Proof: `AllianceMotion::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `b` is `[2, 1024]`.
	/// The range of component `m` is `[4, 100]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_early_approved(b: u32, m: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `699 + b * (1 ±0) + m * (64 ±0) + p * (40 ±0)`
		//  Estimated: `4016 + b * (1 ±0) + m * (66 ±0) + p * (40 ±0)`
		// Minimum execution time: 41_767_000 picoseconds.
		Weight::from_parts(44_128_968, 0)
			.saturating_add(Weight::from_parts(0, 4016))
			// Standard Error: 172
			.saturating_add(Weight::from_parts(2_816, 0).saturating_mul(b.into()))
			// Standard Error: 1_824
			.saturating_add(Weight::from_parts(16_001, 0).saturating_mul(m.into()))
			// Standard Error: 1_778
			.saturating_add(Weight::from_parts(217_559, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(Weight::from_parts(0, 1).saturating_mul(b.into()))
			.saturating_add(Weight::from_parts(0, 66).saturating_mul(m.into()))
			.saturating_add(Weight::from_parts(0, 40).saturating_mul(p.into()))
	}
	/// Storage: `AllianceMotion::Voting` (r:1 w:1)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Members` (r:1 w:0)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Prime` (r:1 w:0)
	/// Proof: `AllianceMotion::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Proposals` (r:1 w:1)
	/// Proof: `AllianceMotion::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::ProposalOf` (r:0 w:1)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `m` is `[4, 100]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_disapproved(m: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `495 + m * (48 ±0) + p * (36 ±0)`
		//  Estimated: `3935 + m * (49 ±0) + p * (36 ±0)`
		// Minimum execution time: 32_514_000 picoseconds.
		Weight::from_parts(32_780_864, 0)
			.saturating_add(Weight::from_parts(0, 3935))
			// Standard Error: 1_414
			.saturating_add(Weight::from_parts(35_156, 0).saturating_mul(m.into()))
			// Standard Error: 1_379
			.saturating_add(Weight::from_parts(212_010, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(4))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(Weight::from_parts(0, 49).saturating_mul(m.into()))
			.saturating_add(Weight::from_parts(0, 36).saturating_mul(p.into()))
	}
	/// Storage: `AllianceMotion::Voting` (r:1 w:1)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Members` (r:1 w:0)
	/// Proof: `AllianceMotion::Members` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Prime` (r:1 w:0)
	/// Proof: `AllianceMotion::Prime` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::ProposalOf` (r:1 w:1)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Proposals` (r:1 w:1)
	/// Proof: `AllianceMotion::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// The range of component `b` is `[2, 1024]`.
	/// The range of component `m` is `[4, 100]`.
	/// The range of component `p` is `[1, 100]`.
	fn close_approved(b: u32, m: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `719 + b * (1 ±0) + m * (64 ±0) + p * (40 ±0)`
		//  Estimated: `4036 + b * (1 ±0) + m * (66 ±0) + p * (40 ±0)`
		// Minimum execution time: 44_616_000 picoseconds.
		Weight::from_parts(45_918_799, 0)
			.saturating_add(Weight::from_parts(0, 4036))
			// Standard Error: 180
			.saturating_add(Weight::from_parts(3_239, 0).saturating_mul(b.into()))
			// Standard Error: 1_911
			.saturating_add(Weight::from_parts(19_863, 0).saturating_mul(m.into()))
			// Standard Error: 1_862
			.saturating_add(Weight::from_parts(225_057, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(Weight::from_parts(0, 1).saturating_mul(b.into()))
			.saturating_add(Weight::from_parts(0, 66).saturating_mul(m.into()))
			.saturating_add(Weight::from_parts(0, 40).saturating_mul(p.into()))
	}
	/// Storage: `AllianceMotion::Proposals` (r:1 w:1)
	/// Proof: `AllianceMotion::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Voting` (r:0 w:1)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::ProposalOf` (r:0 w:1)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `p` is `[1, 100]`.
	fn disapprove_proposal(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `226 + p * (32 ±0)`
		//  Estimated: `1711 + p * (32 ±0)`
		// Minimum execution time: 14_411_000 picoseconds.
		Weight::from_parts(16_195_988, 0)
			.saturating_add(Weight::from_parts(0, 1711))
			// Standard Error: 844
			.saturating_add(Weight::from_parts(169_877, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(Weight::from_parts(0, 32).saturating_mul(p.into()))
	}
	/// Storage: `AllianceMotion::ProposalOf` (r:1 w:1)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::CostOf` (r:1 w:0)
	/// Proof: `AllianceMotion::CostOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Proposals` (r:1 w:1)
	/// Proof: `AllianceMotion::Proposals` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::Voting` (r:0 w:1)
	/// Proof: `AllianceMotion::Voting` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// The range of component `d` is `[0, 1]`.
	/// The range of component `p` is `[1, 100]`.
	fn kill(d: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1497 + p * (36 ±0)`
		//  Estimated: `4896 + d * (123 ±6) + p * (37 ±0)`
		// Minimum execution time: 20_930_000 picoseconds.
		Weight::from_parts(24_552_041, 0)
			.saturating_add(Weight::from_parts(0, 4896))
			// Standard Error: 153_549
			.saturating_add(Weight::from_parts(2_104_624, 0).saturating_mul(d.into()))
			// Standard Error: 2_377
			.saturating_add(Weight::from_parts(241_388, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(3))
			.saturating_add(T::DbWeight::get().writes(3))
			.saturating_add(Weight::from_parts(0, 123).saturating_mul(d.into()))
			.saturating_add(Weight::from_parts(0, 37).saturating_mul(p.into()))
	}
	/// Storage: `AllianceMotion::ProposalOf` (r:1 w:0)
	/// Proof: `AllianceMotion::ProposalOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `AllianceMotion::CostOf` (r:1 w:0)
	/// Proof: `AllianceMotion::CostOf` (`max_values`: None, `max_size`: None, mode: `Measured`)
	fn release_proposal_cost() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `911`
		//  Estimated: `4376`
		// Minimum execution time: 17_120_000 picoseconds.
		Weight::from_parts(17_794_000, 0)
			.saturating_add(Weight::from_parts(0, 4376))
			.saturating_add(T::DbWeight::get().reads(2))
	}
}
