// This file is part of Substrate.

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

//! bounties pallet tests.

#![cfg(test)]

use crate as pallet_bounties;
use crate::{Event as BountiesEvent, *};

use core::cell::RefCell;

use alloc::collections::btree_map::BTreeMap;
use frame_support::{
	derive_impl, parameter_types,
	traits::{tokens::UnityAssetBalanceConversion, ConstU32, ConstU64, OnInitialize},
	PalletId,
	assert_ok
};
use sp_runtime::{traits::IdentityLookup, BuildStorage, Perbill};

type Block = frame_system::mocking::MockBlock<Test>;

thread_local! {
	pub static PAID: RefCell<BTreeMap<(u128, u32), u64>> = RefCell::new(BTreeMap::new());
	pub static STATUS: RefCell<BTreeMap<u64, PaymentStatus>> = RefCell::new(BTreeMap::new());
	pub static LAST_ID: RefCell<u64> = RefCell::new(0u64);

	#[cfg(feature = "runtime-benchmarks")]
	pub static TEST_SPEND_ORIGIN_TRY_SUCCESFUL_ORIGIN_ERR: RefCell<bool> = RefCell::new(false);
}

/// paid balance for a given account and asset ids
pub fn paid(who: u128, asset_id: u32) -> u64 {
	PAID.with(|p| p.borrow().get(&(who, asset_id)).cloned().unwrap_or(0))
}
/// reduce paid balance for a given account and asset ids
fn unpay(who: u128, asset_id: u32, amount: u64) {
	PAID.with(|p| p.borrow_mut().entry((who, asset_id)).or_default().saturating_reduce(amount))
}
/// set status for a given payment id
pub fn set_status(id: u64, s: PaymentStatus) {
	STATUS.with(|m| m.borrow_mut().insert(id, s));
}
// This function directly jumps to a block number, and calls `on_initialize`.
pub fn go_to_block(n: u64) {
	<Test as pallet_treasury::Config>::BlockNumberProvider::set_block_number(n);
	<Treasury as OnInitialize<u64>>::on_initialize(n);
}
pub struct TestPay;
impl Pay for TestPay {
	type Beneficiary = u128;
	type Balance = u64;
	type Id = u64;
	type AssetKind = u32;
	type Error = ();

	fn pay(
		from: &Self::Beneficiary,
		to: &Self::Beneficiary,
		asset_kind: Self::AssetKind,
		amount: Self::Balance,
	) -> Result<Self::Id, Self::Error> {
		let balance_from = Balances::free_balance(*from).saturating_sub(amount);
		assert_ok!(Balances::force_set_balance(
			frame_system::RawOrigin::Root.into(),
			*from,
			balance_from,
		));
		let balance_to = Balances::free_balance(*to).saturating_add(amount);
		assert_ok!(Balances::force_set_balance(
			frame_system::RawOrigin::Root.into(),
			*to,
			balance_to,
		));

		PAID.with(|paid| *paid.borrow_mut().entry((*to, asset_kind)).or_default() += amount);
		Ok(LAST_ID.with(|lid| {
			let x = *lid.borrow();
			lid.replace(x + 1);
			x
		}))
	}
	fn check_payment(id: Self::Id) -> PaymentStatus {
		STATUS.with(|s| s.borrow().get(&id).cloned().unwrap_or(PaymentStatus::Unknown))
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_successful(_: &Self::Beneficiary, _: Self::AssetKind, _: Self::Balance) {}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_concluded(id: Self::Id) {
		set_status(id, PaymentStatus::Failure)
	}
}

frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system,
		Balances: pallet_balances,
		Bounties: pallet_bounties,
		Bounties1: pallet_bounties::<Instance1>,
		Treasury: pallet_treasury,
		Treasury1: pallet_treasury::<Instance1>,
	}
);

parameter_types! {
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

type Balance = u64;

#[derive_impl(frame_system::config_preludes::TestDefaultConfig)]
impl frame_system::Config for Test {
	type AccountId = u128; // u64 is not enough to hold bytes used to generate bounty account
	type Lookup = IdentityLookup<Self::AccountId>;
	type Block = Block;
	type AccountData = pallet_balances::AccountData<u64>;
}

#[derive_impl(pallet_balances::config_preludes::TestDefaultConfig)]
impl pallet_balances::Config for Test {
	type AccountStore = System;
}
parameter_types! {
	pub static Burn: Permill = Permill::from_percent(50);
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
	pub const TreasuryPalletId2: PalletId = PalletId(*b"py/trsr2");
	pub static SpendLimit: Balance = u64::MAX;
	pub static SpendLimit1: Balance = u64::MAX;
	pub TreasuryAccount: u128 = Treasury::account_id();
	pub TreasuryInstance1Account: u128 = Treasury1::account_id();
}

impl pallet_treasury::Config for Test {
	type PalletId = TreasuryPalletId;
	type Currency = pallet_balances::Pallet<Test>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type RuntimeEvent = RuntimeEvent;
	type SpendPeriod = ConstU64<2>;
	type Burn = Burn;
	type BurnDestination = (); // Just gets burned.
	type WeightInfo = ();
	type SpendFunds = ();
	type MaxApprovals = ConstU32<100>;
	type SpendOrigin = frame_system::EnsureRootWithSuccess<Self::AccountId, SpendLimit>;
	type AssetKind = u32;
	type Beneficiary = Self::AccountId;
	type BeneficiaryLookup = IdentityLookup<Self::Beneficiary>;
	type Paymaster = TestPay;
	type BalanceConverter = UnityAssetBalanceConversion;
	type PayoutPeriod = ConstU64<10>;
	type BlockNumberProvider = System;
	#[cfg(feature = "runtime-benchmarks")]
	type BenchmarkHelper = ();
}

impl pallet_treasury::Config<Instance1> for Test {
	type PalletId = TreasuryPalletId2;
	type Currency = pallet_balances::Pallet<Test>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type RuntimeEvent = RuntimeEvent;
	type SpendPeriod = ConstU64<2>;
	type Burn = Burn;
	type BurnDestination = (); // Just gets burned.
	type WeightInfo = ();
	type SpendFunds = ();
	type MaxApprovals = ConstU32<100>;
	type SpendOrigin = frame_system::EnsureRootWithSuccess<Self::AccountId, SpendLimit1>;
	type AssetKind = u32;
	type Beneficiary = Self::AccountId;
	type BeneficiaryLookup = IdentityLookup<Self::Beneficiary>;
	type Paymaster = TestPay;
	type BalanceConverter = UnityAssetBalanceConversion;
	type PayoutPeriod = ConstU64<10>;
	type BlockNumberProvider = System;
	#[cfg(feature = "runtime-benchmarks")]
	type BenchmarkHelper = ();
}

parameter_types! {
	// This will be 50% of the bounty fee.
	pub const CuratorDepositMultiplier: Permill = Permill::from_percent(50);
	pub const CuratorDepositMax: Balance = 1_000;
	pub const CuratorDepositMin: Balance = 3;

}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type BountyDepositBase = ConstU64<80>;
	type BountyDepositPayoutDelay = ConstU64<3>;
	type BountyUpdatePeriod = ConstU64<20>;
	type CuratorDepositMultiplier = CuratorDepositMultiplier;
	type CuratorDepositMax = CuratorDepositMax;
	type CuratorDepositMin = CuratorDepositMin;
	type BountyValueMinimum = ConstU64<1>;
	type DataDepositPerByte = ConstU64<1>;
	type MaximumReasonLength = ConstU32<16384>;
	type WeightInfo = ();
	type ChildBountyManager = ();
	type OnSlash = ();
	#[cfg(feature = "runtime-benchmarks")]
	type BenchmarkHelper = ();
}

impl Config<Instance1> for Test {
	type RuntimeEvent = RuntimeEvent;
	type BountyDepositBase = ConstU64<80>;
	type BountyDepositPayoutDelay = ConstU64<3>;
	type BountyUpdatePeriod = ConstU64<20>;
	type CuratorDepositMultiplier = CuratorDepositMultiplier;
	type CuratorDepositMax = CuratorDepositMax;
	type CuratorDepositMin = CuratorDepositMin;
	type BountyValueMinimum = ConstU64<1>;
	type DataDepositPerByte = ConstU64<1>;
	type MaximumReasonLength = ConstU32<16384>;
	type WeightInfo = ();
	type ChildBountyManager = ();
	type OnSlash = ();
	#[cfg(feature = "runtime-benchmarks")]
	type BenchmarkHelper = ();
}

pub type TreasuryError = pallet_treasury::Error<Test>;
pub type TreasuryError1 = pallet_treasury::Error<Test, Instance1>;
pub type TreasuryEvent = pallet_treasury::Event<Test>;
pub type TreasuryEvent1 = pallet_treasury::Event<Test, Instance1>;


pub struct ExtBuilder {}

impl Default for ExtBuilder {
	fn default() -> Self {
		Self {}
	}
}

impl ExtBuilder {
	pub fn build(self) -> sp_io::TestExternalities {
		let mut ext: sp_io::TestExternalities = RuntimeGenesisConfig {
			system: frame_system::GenesisConfig::default(),
			balances: pallet_balances::GenesisConfig {
				balances: vec![(0, 100), (1, 98), (2, 1)],
				..Default::default()
			},
			treasury: Default::default(),
			treasury_1: Default::default(),
		}
		.build_storage()
		.unwrap()
		.into();
		ext.execute_with(|| {
			<Test as pallet_treasury::Config>::BlockNumberProvider::set_block_number(1)
		});
		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
			Bounties::do_try_state().expect("All invariants must hold after a test");
			Bounties1::do_try_state().expect("All invariants must hold after a test");
		})
	}
}

pub fn last_events(n: usize) -> Vec<BountiesEvent<Test>> {
	let mut res = System::events()
		.into_iter()
		.rev()
		.filter_map(
			|e| if let RuntimeEvent::Bounties(inner) = e.event { Some(inner) } else { None },
		)
		.take(n)
		.collect::<Vec<_>>();
	res.reverse();
	res
}

pub fn last_event() -> BountiesEvent<Test> {
	last_events(1).into_iter().next().unwrap()
}

pub fn expect_events(e: Vec<BountiesEvent<Test>>) {
	assert_eq!(last_events(e.len()), e);
}

pub fn get_payment_id(i: BountyIndex) -> Option<u64> {
	let bounty = pallet_bounties::Bounties::<Test>::get(i).expect("no bounty");

	match bounty.status {
		BountyStatus::Approved { payment_status: PaymentState::Attempted { id } } => Some(id),
		BountyStatus::ApprovedWithCurator { payment_status: PaymentState::Attempted { id }, .. } => Some(id),
		_ => None,
	}
}

pub fn get_payment_ids(i: BountyIndex) -> Option<(u64, u64)> {
    let bounty = pallet_bounties::Bounties::<Test>::get(i).expect("no bounty");

    match bounty.status {
        BountyStatus::PayoutAttempted { curator_stash, beneficiary, curator: _ } => {
            match (curator_stash.1, beneficiary.1) {
                (PaymentState::Attempted { id: curator_payment_id }, PaymentState::Attempted { id: beneficiary_payment_id }) => {
                    Some((curator_payment_id, beneficiary_payment_id))
                },
                _ => None,
            }
        },
        _ => None,
    }
}