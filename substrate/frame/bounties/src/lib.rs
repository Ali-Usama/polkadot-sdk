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

//! # Bounties Module ( pallet-bounties )
//!
//! ## Bounty
//!
//! > NOTE: This pallet is tightly coupled with pallet-treasury.
//!
//! A Bounty Spending is a reward for a specified body of work - or specified set of objectives -
//! that needs to be executed for a predefined Treasury amount to be paid out. A curator is assigned
//! after the bounty is approved and funded by Council, to be delegated with the responsibility of
//! assigning a payout address once the specified set of objectives is completed.
//!
//! After the Council has activated a bounty, it delegates the work that requires expertise to a
//! curator in exchange of a deposit. Once the curator accepts the bounty, they get to close the
//! active bounty. Closing the active bounty enacts a delayed payout to the payout address, the
//! curator fee and the return of the curator deposit. The delay allows for intervention through
//! regular democracy. The Council gets to unassign the curator, resulting in a new curator
//! election. The Council also gets to cancel the bounty if deemed necessary before assigning a
//! curator or once the bounty is active or payout is pending, resulting in the slash of the
//! curator's deposit.
//!
//! This pallet may opt into using a [`ChildBountyManager`] that enables bounties to be split into
//! sub-bounties, as children of an established bounty (called the parent in the context of it's
//! children).
//!
//! > NOTE: The parent bounty cannot be closed if it has a non-zero number of it has active child
//! > bounties associated with it.
//!
//! ### Terminology
//!
//! Bounty:
//!
//! - **Bounty spending proposal:** A proposal to reward a predefined body of work upon completion
//!   by the Treasury.
//! - **Proposer:** An account proposing a bounty spending.
//! - **Curator:** An account managing the bounty and assigning a payout address receiving the
//!   reward for the completion of work.
//! - **Deposit:** The amount held on deposit for placing a bounty proposal plus the amount held on
//!   deposit per byte within the bounty description.
//! - **Curator deposit:** The payment from a candidate willing to curate an approved bounty. The
//!   deposit is returned when/if the bounty is completed.
//! - **Bounty value:** The total amount that should be paid to the Payout Address if the bounty is
//!   rewarded.
//! - **Payout address:** The account to which the total or part of the bounty is assigned to.
//! - **Payout Delay:** The delay period for which a bounty beneficiary needs to wait before
//!   claiming.
//! - **Curator fee:** The reserved upfront payment for a curator for work related to the bounty.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! Bounty protocol:
//!
//! - `propose_bounty` - Propose a specific treasury amount to be earmarked for a predefined set of
//!   tasks and stake the required deposit.
//! - `approve_bounty` - Accept a specific treasury amount to be earmarked for a predefined body of
//!   work.
//! - `propose_curator` - Assign an account to a bounty as candidate curator.
//! - `approve_bounty_with_curator` - Accept a specific treasury amount for a predefined body of
//!   work with assigned candidate curator account.
//! - `accept_curator` - Accept a bounty assignment from the Council, setting a curator deposit.
//! - `extend_bounty_expiry` - Extend the expiry block number of the bounty and stay active.
//! - `award_bounty` - Close and pay out the specified amount for the completed work.
//! - `claim_bounty` - Claim a specific bounty amount from the Payout Address.
//! - `unassign_curator` - Unassign an accepted curator from a specific earmark.
//! - `close_bounty` - Cancel the earmark for a specific treasury amount and close the bounty.
//! - `process_payment` - Retry a failed payment for bounty funding, curator and beneficiary payout
//!   or refund.
//! - `check_payment_status` - Check and update the current state of the bounty funding, payout or
//!   refund.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod migrations;
#[cfg(any(test, feature = "runtime-benchmarks"))]
mod tests;
pub mod weights;
pub use pallet::*;
pub use weights::WeightInfo;

extern crate alloc;
use alloc::{collections::btree_map::BTreeMap, vec::Vec};
use frame_support::{
	dispatch::{DispatchResult, DispatchResultWithPostInfo},
	dispatch_context::with_context,
	pallet_prelude::*,
	traits::{
		tokens::{ConversionFromAssetBalance, Pay, PaymentStatus},
		Currency, EnsureOrigin, Get, OnUnbalanced, ReservableCurrency,
	},
};
use frame_system::pallet_prelude::{
	ensure_signed, BlockNumberFor as SystemBlockNumberFor, OriginFor,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{AccountIdConversion, BadOrigin, BlockNumberProvider, Saturating, StaticLookup, Zero},
	Permill, RuntimeDebug,
};

type DepositBalanceOf<T, I = ()> = pallet_treasury::BalanceOf<T, I>;
type BountyBalanceOf<T, I = ()> = pallet_treasury::AssetBalanceOf<T, I>;
type BeneficiaryLookupOf<T, I = ()> = pallet_treasury::BeneficiaryLookupOf<T, I>;
type PaymentIdOf<T, I = ()> = <<T as pallet_treasury::Config<I>>::Paymaster as Pay>::Id;

/// An index of a bounty. Just a `u32`.
pub type BountyIndex = u32;

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;
type BountyOf<T, I> = Bounty<
	<T as frame_system::Config>::AccountId,
	DepositBalanceOf<T, I>,
	BountyBalanceOf<T, I>,
	BlockNumberFor<T, I>,
	<T as pallet_treasury::Config<I>>::AssetKind,
	PaymentIdOf<T, I>,
	<T as pallet_treasury::Config<I>>::Beneficiary,
>;
type BountyStatusOf<T, I> = BountyStatus<
	<T as frame_system::Config>::AccountId,
	BlockNumberFor<T, I>,
	PaymentIdOf<T, I>,
	<T as pallet_treasury::Config<I>>::Beneficiary,
>;
type BlockNumberFor<T, I = ()> =
	<<T as pallet_treasury::Config<I>>::BlockNumberProvider as BlockNumberProvider>::BlockNumber;

/// A bounty proposal.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub struct Bounty<
	AccountId,
	NativeBalance,
	BountyBalance,
	BlockNumber,
	AssetKind,
	PaymentId,
	Beneficiary,
> where
	Beneficiary: Clone,
	PaymentId: Clone,
{
	/// The account proposing it.
	proposer: AccountId,
	// TODO: new filed, migration required.
	/// The kind of asset this bounty is rewarded in.
	pub asset_kind: AssetKind,
	/// The (total) amount of the `asset_kind` that should be paid if the bounty is rewarded.
	value: BountyBalance,
	/// The curator fee in the `asset_kind`. Included in value.
	fee: BountyBalance,
	/// The deposit of curator.
	///
	/// The asset class determined by the [`pallet_treasury::Config::Currency`].
	curator_deposit: NativeBalance,
	/// The amount held on deposit (reserved) for making this proposal.
	///
	/// The asset class determined by the [`pallet_treasury::Config::Currency`].
	bond: NativeBalance,
	/// The status of this bounty.
	status: BountyStatus<AccountId, BlockNumber, PaymentId, Beneficiary>,
}

impl<
		AccountId: PartialEq + Clone + Ord,
		NativeBalance,
		BountyBalance,
		BlockNumber: Clone,
		AssetKind,
		PaymentId: Clone,
		Beneficiary: Clone,
	> Bounty<AccountId, NativeBalance, BountyBalance, BlockNumber, AssetKind, PaymentId, Beneficiary>
{
	/// Getter for bounty status, to be used for child bounties.
	pub fn get_status(&self) -> BountyStatus<AccountId, BlockNumber, PaymentId, Beneficiary> {
		self.status.clone()
	}
}

// TODO: breaking changes to the stored type, migration required.

/// The status of a bounty proposal.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum BountyStatus<AccountId, BlockNumber, PaymentId, Beneficiary>
where
	Beneficiary: Clone,
	PaymentId: Clone,
{
	/// The bounty is proposed and waiting for approval.
	Proposed,
	/// The bounty is approved and waiting to confirm the funds allocation.
	Approved {
		/// The status of the bounty amount transfer from the source (e.g. Treasury) to
		/// the bounty account.
		///
		/// Once the payment is confirmed, the bounty will transition to either
		/// [`BountyStatus::Funded`]
		payment_status: PaymentState<PaymentId>,
	},
	/// The bounty is funded and waiting for curator assignment.
	Funded,
	/// A curator has been proposed. Waiting for acceptance from the curator.
	CuratorProposed {
		/// The assigned curator of this bounty.
		curator: AccountId,
	},
	/// The bounty is active and waiting to be awarded.
	Active {
		/// The curator of this bounty.
		curator: AccountId,
		/// The curator's stash account used as a fee destination.
		curator_stash: Beneficiary,
		/// An update from the curator is due by this block, else they are considered inactive.
		update_due: BlockNumber,
	},
	/// The bounty is awarded and waiting to released after a delay.
	PendingPayout {
		/// The curator of this bounty.
		curator: AccountId,
		/// The curator's stash account used as a fee destination.
		curator_stash: Beneficiary,
		/// The beneficiary of the bounty.
		beneficiary: Beneficiary,
		/// When the bounty can be claimed.
		unlock_at: BlockNumber,
	},
	/// The bounty is approved with a curator and waiting to confirm the funds allocation.
	ApprovedWithCurator {
		/// The assigned curator of this bounty.
		curator: AccountId,
		/// The status of the bounty amount transfer from the source (e.g. Treasury) to
		/// the bounty account.
		///
		/// Once the payment is confirmed, the bounty will transition to
		/// [`BountyStatus::CuratorProposed`], depending on the value
		payment_status: PaymentState<PaymentId>,
	},
	/// The bounty payout has been attempted.
	///
	/// In case of a failed payout, the payout can be retried. Once the payout is successful, the
	/// bounty is completed and removed from the storage.
	PayoutAttempted {
		/// The curator of this bounty.
		curator: AccountId,
		/// The curator's stash account with the payout status.
		curator_stash: (Beneficiary, PaymentState<PaymentId>),
		/// The beneficiary's stash account with the payout status.
		beneficiary: (Beneficiary, PaymentState<PaymentId>),
	},
	/// The bounty is closed, and the funds are being refunded to the original source (e.g.,
	/// Treasury).
	RefundAttempted {
		/// The refund status.
		///
		/// Once the refund is successful, the bounty is removed from the storage.
		payment_status: PaymentState<PaymentId>,
	},
}

/// The state of the payment claim.
#[derive(Encode, Decode, Clone, PartialEq, Eq, MaxEncodedLen, RuntimeDebug, TypeInfo)]
pub enum PaymentState<Id> {
	/// Pending claim.
	Pending,
	/// Payment attempted with a payment identifier.
	Attempted { id: Id },
	/// Payment failed.
	Failed,
	/// Payment succeeded.
	Succeeded,
}

/// The child bounty manager.
pub trait ChildBountyManager<Balance> {
	/// Get the active child bounties for a parent bounty.
	fn child_bounties_count(bounty_id: BountyIndex) -> BountyIndex;

	/// Take total curator fees of children-bounty curators.
	fn children_curator_fees(bounty_id: BountyIndex) -> Balance;

	/// Hook called when a parent bounty is removed.
	fn bounty_removed(bounty_id: BountyIndex);
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	const STORAGE_VERSION: StorageVersion = StorageVersion::new(4);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config + pallet_treasury::Config<I> {
		// TODO: since we break the API with this iteration it may be reasonable to migrate to
		// `Considerations` and remove old config parameters relater to deposits. This is optional
		// for current PR.

		/// The amount held on deposit for placing a bounty proposal.
		#[pallet::constant]
		type BountyDepositBase: Get<DepositBalanceOf<Self, I>>;

		/// The delay period for which a bounty beneficiary need to wait before claim the payout.
		#[pallet::constant]
		type BountyDepositPayoutDelay: Get<BlockNumberFor<Self, I>>;

		/// Bounty duration in blocks.
		#[pallet::constant]
		type BountyUpdatePeriod: Get<BlockNumberFor<Self, I>>;

		/// The curator deposit is calculated as a percentage of the curator fee.
		///
		/// This deposit has optional upper and lower bounds with `CuratorDepositMax` and
		/// `CuratorDepositMin`.
		#[pallet::constant]
		type CuratorDepositMultiplier: Get<Permill>;

		/// Maximum amount of funds that should be placed in a deposit for making a proposal.
		#[pallet::constant]
		type CuratorDepositMax: Get<Option<DepositBalanceOf<Self, I>>>;

		/// Minimum amount of funds that should be placed in a deposit for making a proposal.
		#[pallet::constant]
		type CuratorDepositMin: Get<Option<DepositBalanceOf<Self, I>>>;

		/// Minimum value for a bounty.
		#[pallet::constant]
		type BountyValueMinimum: Get<DepositBalanceOf<Self, I>>;

		/// The amount held on deposit per byte within the tip report reason or bounty description.
		#[pallet::constant]
		type DataDepositPerByte: Get<DepositBalanceOf<Self, I>>;

		#[cfg(feature = "runtime-benchmarks")]
		type BenchmarkHelper: benchmarking::ArgumentsFactory<Self::AssetKind>;

		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Maximum acceptable reason length.
		///
		/// Benchmarks depend on this value, be sure to update weights file when changing this value
		#[pallet::constant]
		type MaximumReasonLength: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The child bounty manager.
		type ChildBountyManager: ChildBountyManager<BountyBalanceOf<Self, I>>;

		/// Handler for the unbalanced decrease when slashing for a rejected bounty.
		type OnSlash: OnUnbalanced<pallet_treasury::NegativeImbalanceOf<Self, I>>;
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Proposer's balance is too low.
		InsufficientProposersBalance,
		/// No proposal or bounty at that index.
		InvalidIndex,
		/// The reason given is just too big.
		ReasonTooBig,
		/// The bounty status is unexpected.
		UnexpectedStatus,
		/// Require bounty curator.
		RequireCurator,
		/// Invalid bounty value.
		InvalidValue,
		/// Invalid bounty fee.
		InvalidFee,
		/// A bounty payout is pending.
		/// To cancel the bounty, you must unassign and slash the curator.
		PendingPayout,
		/// The bounties cannot be claimed/closed because it's still in the countdown period.
		Premature,
		/// The bounty cannot be closed because it has active child bounties.
		HasActiveChildBounty,
		/// Too many approvals are already queued.
		TooManyQueued,
		/// There was issue with funding the bounty
		FundingError,
		/// Bounty funding has not concluded yet
		FundingInconclusive,
		/// There was issue paying out the bounty
		PayoutError,
		/// No progress in payouts was made
		PayoutInconclusive,
		/// There was issue with refunding the bounty
		RefundError,
		/// No progress was made processing a refund
		RefundInconclusive,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// New bounty proposal.
		BountyProposed { index: BountyIndex },
		/// A bounty proposal was rejected; funds were slashed.
		BountyRejected { index: BountyIndex, bond: DepositBalanceOf<T, I> },
		/// A bounty proposal is funded and became active.
		BountyBecameActive { index: BountyIndex },
		/// A bounty is awarded to a beneficiary.
		BountyAwarded { index: BountyIndex, beneficiary: T::Beneficiary },
		/// A bounty is claimed by beneficiary.
		BountyClaimed {
			index: BountyIndex,
			asset_kind: T::AssetKind,
			asset_payout: BountyBalanceOf<T, I>,
			beneficiary: T::Beneficiary,
		},
		/// A bounty is cancelled.
		BountyCanceled { index: BountyIndex },
		/// A bounty expiry is extended.
		BountyExtended { index: BountyIndex },
		/// A bounty is approved.
		BountyApproved { index: BountyIndex },
		/// A bounty curator is proposed.
		CuratorProposed { bounty_id: BountyIndex, curator: T::AccountId },
		/// A bounty curator is unassigned.
		CuratorUnassigned { bounty_id: BountyIndex },
		/// A bounty curator is accepted.
		CuratorAccepted { bounty_id: BountyIndex, curator: T::AccountId },
	}

	/// Number of bounty proposals that have been made.
	#[pallet::storage]
	pub type BountyCount<T: Config<I>, I: 'static = ()> = StorageValue<_, BountyIndex, ValueQuery>;

	/// Bounties that have been made.
	#[pallet::storage]
	pub type Bounties<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, BountyIndex, BountyOf<T, I>>;

	/// The description of each bounty.
	#[pallet::storage]
	pub type BountyDescriptions<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, BountyIndex, BoundedVec<u8, T::MaximumReasonLength>>;

	// Tiago: how to remove if it is used in migrations/v4.rs?
	// TODO: most probably wont be needed, review and remove if not needed.
	/// Bounty indices that have been approved but not yet funded.
	#[pallet::storage]
	#[allow(deprecated)]
	pub type BountyApprovals<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BoundedVec<BountyIndex, T::MaxApprovals>, ValueQuery>;

	#[derive(Default)]
	struct SpendContext<Balance> {
		spend_in_context: BTreeMap<Balance, Balance>,
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Propose a new bounty.
		///
		/// ## Dispatch Origin
		/// The dispatch origin for this call must be _Signed_.
		///
		/// ## Details
		/// - A deposit will be reserved from the origin account, as well as `DataDepositPerByte`
		///   for each byte in `description`. It will be unreserved upon approval, or slashed when
		///   rejected.
		///
		/// ### Parameters
		/// - `asset_kind`: An indicator of the specific asset class to be spent.
		/// - `value`: The total payment amount of this bounty, curator fee included.
		/// - `description`: The description of this bounty.
		///
		/// ## Events
		/// Emits [`Event::BountyProposed`] if successful.
		#[pallet::call_index(0)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::propose_bounty(description.len() as u32))]
		pub fn propose_bounty(
			origin: OriginFor<T>,
			asset_kind: Box<T::AssetKind>,
			// Tiago: I propose just using pallet_treasury::AssetBalanceOf<T, I>.
			#[pallet::compact] value: BountyBalanceOf<T, I>,
			description: Vec<u8>,
		) -> DispatchResult {
			let proposer = ensure_signed(origin)?;
			Self::create_bounty(proposer, description, *asset_kind, value)?;
			Ok(())
		}

		/// Approves a bounty proposal, transfering funds from the treasury to the bounty account.
		///
		/// ## Dispatch Origin
		/// Must be [`Config::SpendOrigin`] with the `Success` value being at least
		/// the converted native amount of the bounty. The bounty value is validated
		/// against the maximum spendable amount of the [`Config::SpendOrigin`].
		///
		/// ## Details
		/// - The bounty must be in the `Proposed` state.
		/// - The `SpendOrigin` must have sufficient permissions to approve the bounty.
		/// - If the payment is successful, the bounty status will be updated to `Funded` and the
		/// original deposit will be returned.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty to be approved.
		///
		/// ## Events
		/// Emits [`Event::BountyApproved`] if successful.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(1)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::approve_bounty())]
		pub fn approve_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResult {
			let max_amount = T::SpendOrigin::ensure_origin(origin)?;
			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;
				let native_amount =
					<T as pallet_treasury::Config<I>>::BalanceConverter::from_asset_balance(
						bounty.value,
						bounty.asset_kind.clone(),
					)
					.map_err(|_| pallet_treasury::Error::<T, I>::FailedToConvertBalance)?;
				ensure!(
					native_amount <= max_amount,
					pallet_treasury::Error::<T, I>::InsufficientPermission
				);
				ensure!(bounty.status == BountyStatus::Proposed, Error::<T, I>::UnexpectedStatus);

				// Tiago: is this the best way to use the SpendContext?
				with_context::<SpendContext<DepositBalanceOf<T, I>>, _>(|v| {
					let context = v.or_default();
					let spend = context.spend_in_context.entry(max_amount).or_default();

					if spend.checked_add(&native_amount).map(|s| s > max_amount).unwrap_or(true) {
						Err(pallet_treasury::Error::<T, I>::InsufficientPermission)
					} else {
						*spend = spend.saturating_add(native_amount);
						Ok(())
					}
				})
				.unwrap_or(Ok(()))?;

				let bounty_account = Self::bounty_account_id(bounty_id);
				let treasury_account = Self::account_id();
				let payment_id = T::Paymaster::pay(
					&treasury_account,
					&bounty_account,
					bounty.asset_kind.clone(),
					bounty.value,
				)
				.map_err(|_| Error::<T, I>::FundingError)?;

				bounty.status = BountyStatus::Approved {
					payment_status: PaymentState::Attempted { id: payment_id },
				};

				Ok(())
			})?;

			Self::deposit_event(Event::<T, I>::BountyApproved { index: bounty_id });
			Ok(())
		}

		/// Propose a curator to a funded bounty.
		///
		/// ## Dispatch Origin
		/// Must be called from `T::SpendOrigin`.
		///
		/// ## Details
		/// - The bounty must be in the `Funded` state.
		/// - The `SpendOrigin` must have sufficient permissions to propose the curator.
		/// - The curator fee must be less than the total bounty value.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty to propose a curator for.
		/// - `curator`: The account to be proposed as the curator.
		/// - `fee`: The curator fee.
		///
		/// ## Events
		/// Emits [`Event::CuratorProposed`] if successful.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(2)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::propose_curator())]
		pub fn propose_curator(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
			curator: AccountIdLookupOf<T>,
			#[pallet::compact] fee: BountyBalanceOf<T, I>,
		) -> DispatchResult {
			let max_amount = T::SpendOrigin::ensure_origin(origin)?;

			let curator = T::Lookup::lookup(curator)?;
			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;
				let native_amount =
					<T as pallet_treasury::Config<I>>::BalanceConverter::from_asset_balance(
						bounty.value,
						bounty.asset_kind.clone(),
					)
					.map_err(|_| pallet_treasury::Error::<T, I>::FailedToConvertBalance)?;
				ensure!(
					native_amount <= max_amount,
					pallet_treasury::Error::<T, I>::InsufficientPermission
				);

				// Tiago: maybe we should come up with a different error
				if bounty.status != BountyStatus::Funded {
					return Err(Error::<T, I>::UnexpectedStatus.into());
				}

				ensure!(fee < bounty.value, Error::<T, I>::InvalidFee);

				bounty.status = BountyStatus::CuratorProposed { curator: curator.clone() };
				bounty.fee = fee;

				Self::deposit_event(Event::<T, I>::CuratorProposed { bounty_id, curator });

				Ok(())
			})?;
			Ok(())
		}

		/// Unassign curator from a bounty.
		///
		/// ## Dispatch Origin
		/// This function can only be called by the `RejectOrigin` or a signed origin.
		///
		/// ## Details
		/// - If this function is called by the `RejectOrigin`, we assume that the curator is
		///   malicious or inactive. As a result, we will slash the curator when possible.
		/// - If the origin is the curator, we take this as a sign they are unable to do their job
		///   and
		/// they willingly give up. We could slash them, but for now we allow them to recover their
		/// deposit and exit without issue. (We may want to change this if it is abused.)
		/// - The origin can be anyone if and only if the curator is "inactive". This allows
		/// anyone in the community to call out that a curator is not doing their due diligence, and
		/// we should pick a new curator. In this case the curator should also be slashed.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty from which to unassign the curator.
		///
		/// ## Events
		/// Emits [`Event::CuratorUnassigned`] if successful.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(3)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::unassign_curator())]
		pub fn unassign_curator(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResult {
			let maybe_sender = ensure_signed(origin.clone())
				.map(Some)
				.or_else(|_| T::RejectOrigin::ensure_origin(origin).map(|_| None))?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

				let slash_curator =
					|curator: &T::AccountId, curator_deposit: &mut DepositBalanceOf<T, I>| {
						let imbalance = T::Currency::slash_reserved(curator, *curator_deposit).0;
						T::OnSlash::on_unbalanced(imbalance);
						*curator_deposit = Zero::zero();
					};

				match bounty.status {
					BountyStatus::Proposed |
					BountyStatus::Approved { .. } |
					BountyStatus::Funded |
					BountyStatus::PayoutAttempted { .. } |
					BountyStatus::RefundAttempted { .. } => {
						// No curator to unassign at this point.
						return Err(Error::<T, I>::UnexpectedStatus.into());
					},
					BountyStatus::ApprovedWithCurator { ref curator, ref payment_status } => {
						// Bounty not yet funded, but bounty was approved with curator.
						// `RejectOrigin` or curator himself can unassign from this bounty.
						ensure!(maybe_sender.map_or(true, |sender| sender == *curator), BadOrigin);
						// This state can only be while the bounty is not yet funded so we return
						// bounty to the `Approved` state without curator
						bounty.status =
							BountyStatus::Approved { payment_status: payment_status.clone() };
						return Ok(());
					},
					BountyStatus::CuratorProposed { ref curator } => {
						// A curator has been proposed, but not accepted yet.
						// Either `RejectOrigin` or the proposed curator can unassign the curator.
						ensure!(maybe_sender.map_or(true, |sender| sender == *curator), BadOrigin);
					},
					BountyStatus::Active { ref curator, ref update_due, .. } => {
						// The bounty is active.
						match maybe_sender {
							// If the `RejectOrigin` is calling this function, slash the curator.
							None => {
								slash_curator(curator, &mut bounty.curator_deposit);
								// Continue to change bounty status below...
							},
							Some(sender) => {
								// If the sender is not the curator, and the curator is inactive,
								// slash the curator.
								if sender != *curator {
									let block_number = Self::treasury_block_number();
									if *update_due < block_number {
										slash_curator(curator, &mut bounty.curator_deposit);
									// Continue to change bounty status below...
									} else {
										// Curator has more time to give an update.
										return Err(Error::<T, I>::Premature.into());
									}
								} else {
									// Else this is the curator, willingly giving up their role.
									// Give back their deposit.
									let err_amount =
										T::Currency::unreserve(curator, bounty.curator_deposit);
									debug_assert!(err_amount.is_zero());
									bounty.curator_deposit = Zero::zero();
									// Continue to change bounty status below...
								}
							},
						}
					},
					BountyStatus::PendingPayout { ref curator, .. } => {
						// The bounty is pending payout, so only council can unassign a curator.
						// By doing so, they are claiming the curator is acting maliciously, so
						// we slash the curator.
						ensure!(maybe_sender.is_none(), BadOrigin);
						slash_curator(curator, &mut bounty.curator_deposit);
						// Continue to change bounty status below...
					},
				};

				bounty.status = BountyStatus::Funded;
				Ok(())
			})?;

			Self::deposit_event(Event::<T, I>::CuratorUnassigned { bounty_id });
			Ok(())
		}

		/// Accept the curator role for a bounty.
		/// A deposit will be reserved from the curator and refunded upon successful payout.
		///
		/// ## Dispatch Origin
		/// Must be signed by the proposed curator.
		///
		/// ## Details
		/// - The bounty must be in the `CuratorProposed` state.
		/// - The curator must accept the role by calling this function.
		/// - The deposit will be refunded upon successful payout of the bounty.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty for which the curator is accepting the role.
		/// - `stash`: The curator's stash account that will receive the curator fee.
		///
		/// ## Events
		/// Emits [`Event::CuratorAccepted`] if successful.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(4)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::accept_curator())]
		pub fn accept_curator(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
			stash: BeneficiaryLookupOf<T, I>,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;
			let stash = T::BeneficiaryLookup::lookup(stash)?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

				match bounty.status {
					BountyStatus::CuratorProposed { ref curator } => {
						ensure!(signer == *curator, Error::<T, I>::RequireCurator);

						let deposit = Self::calculate_curator_deposit(
							&bounty.fee,
							bounty.asset_kind.clone(),
						)?;
						T::Currency::reserve(curator, deposit)?;

						bounty.curator_deposit = deposit;

						let update_due =
							Self::treasury_block_number() + T::BountyUpdatePeriod::get();

						bounty.status = BountyStatus::Active {
							curator: curator.clone(),
							curator_stash: stash,
							update_due,
						};

						Self::deposit_event(Event::<T, I>::CuratorAccepted {
							bounty_id,
							curator: signer,
						});
						Ok(())
					},
					_ => Err(Error::<T, I>::UnexpectedStatus.into()),
				}
			})?;
			Ok(())
		}

		/// Award bounty to a beneficiary account. The beneficiary will be able to claim the funds
		/// after `BountyDepositPayoutDelay`.
		///
		/// ## Dispatch Origin
		/// Must be signed by the curator of this bounty.
		///
		/// ## Details
		/// - The bounty must be in the `Active` state.
		/// - The curator must call this function to award the bounty to a beneficiary.
		/// - The funds will be locked until the payout delay has passed.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty to be awarded.
		/// - `beneficiary`: The account to be awarded the bounty.
		///
		/// ## Events
		/// Emits [`Event::BountyAwarded`] if successful.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(5)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::award_bounty())]
		pub fn award_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
			beneficiary: BeneficiaryLookupOf<T, I>,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;
			let beneficiary = T::BeneficiaryLookup::lookup(beneficiary)?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

				// Ensure no active child bounties before processing the call.
				ensure!(
					T::ChildBountyManager::child_bounties_count(bounty_id) == 0,
					Error::<T, I>::HasActiveChildBounty
				);

				match &bounty.status {
					BountyStatus::Active { curator, curator_stash, .. } => {
						ensure!(signer == *curator, Error::<T, I>::RequireCurator);
						bounty.status = BountyStatus::PendingPayout {
							curator: signer,
							beneficiary: beneficiary.clone(),
							unlock_at: Self::treasury_block_number() +
								T::BountyDepositPayoutDelay::get(),
							curator_stash: curator_stash.clone(),
						};
					},
					_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
				}

				Ok(())
			})?;

			Self::deposit_event(Event::<T, I>::BountyAwarded { index: bounty_id, beneficiary });
			Ok(())
		}

		/// Claim the payout from an awarded bounty after the payout delay has passed.
		///
		/// ## Dispatch Origin
		/// Must be signed.
		///
		/// ## Details
		/// - The bounty must be in the `PendingPayout` state.
		/// - The funds will be transferred to the beneficiary and the curator.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty to be claimed.
		///
		/// ## Events
		/// Emits [`Event::BountyClaimed`] if successful.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(6)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::claim_bounty())]
		pub fn claim_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?; // anyone can trigger claim

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

				if let BountyStatus::PendingPayout {
					curator,
					beneficiary,
					unlock_at,
					curator_stash,
				} = &bounty.status
				{
					ensure!(Self::treasury_block_number() >= *unlock_at, Error::<T, I>::Premature);

					let (final_fee, payout) =
						Self::calculate_curator_fee_and_payout(bounty_id, bounty.fee, bounty.value);
					let bounty_account = Self::bounty_account_id(bounty_id);

					let curator_payment_id = T::Paymaster::pay(
						&bounty_account,
						&curator_stash,
						bounty.asset_kind.clone(),
						final_fee,
					)
					.map_err(|_| Error::<T, I>::PayoutError)?;

					let beneficiary_payment_id = T::Paymaster::pay(
						&bounty_account,
						&beneficiary,
						bounty.asset_kind.clone(),
						payout,
					)
					.map_err(|_| Error::<T, I>::PayoutError)?;

					bounty.status = BountyStatus::PayoutAttempted {
						curator: curator.clone(),
						curator_stash: (
							curator_stash.clone(),
							PaymentState::Attempted { id: curator_payment_id },
						),
						beneficiary: (
							beneficiary.clone(),
							PaymentState::Attempted { id: beneficiary_payment_id },
						),
					};

					Ok(())
				} else {
					Err(Error::<T, I>::UnexpectedStatus.into())
				}
			})?;
			Ok(())
		}

		/// Cancel a proposed or active bounty. All the funds will be sent to treasury and
		/// the curator deposit will be unreserved if possible.
		///
		/// ## Dispatch Origin
		/// Only `T::RejectOrigin` is able to cancel a bounty.
		///
		/// ## Details
		/// - If the bounty is in the `Proposed` state, the deposit will be slashed, and the bounty
		///   will be removed.
		/// - If the bounty is in the `Active` state, the curator’s deposit will be unreserved.
		/// - If the bounty is already in the payout phase, it cannot be canceled.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty to cancel.
		///
		/// ## Events
		/// - Emits `BountyRejected` if the bounty was in the `Proposed` state.
		/// - Emits `RefundAttempted` if the bounty was already funded and is being refunded.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(7)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::close_bounty_proposed()
			.max(<T as Config<I>>::WeightInfo::close_bounty_active()))]
		pub fn close_bounty(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResultWithPostInfo {
			T::RejectOrigin::ensure_origin(origin)?;

			Bounties::<T, I>::try_mutate_exists(
				bounty_id,
				|maybe_bounty| -> DispatchResultWithPostInfo {
					let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

					// Ensure no active child bounties before processing the call.
					ensure!(
						T::ChildBountyManager::child_bounties_count(bounty_id) == 0,
						Error::<T, I>::HasActiveChildBounty
					);

					match &bounty.status {
						BountyStatus::Proposed => {
							// The reject origin would like to cancel a proposed bounty.
							BountyDescriptions::<T, I>::remove(bounty_id);
							let value = bounty.bond;
							let imbalance = T::Currency::slash_reserved(&bounty.proposer, value).0;
							T::OnSlash::on_unbalanced(imbalance);
							*maybe_bounty = None;

							Self::deposit_event(Event::<T, I>::BountyRejected {
								index: bounty_id,
								bond: value,
							});
							// Return early, nothing else to do.
							return Ok(
								Some(<T as Config<I>>::WeightInfo::close_bounty_proposed()).into()
							)
						},
						BountyStatus::Approved { .. } |
						BountyStatus::ApprovedWithCurator { .. } => {
							// For weight reasons, we don't allow a council to cancel in this phase.
							// We ask for them to wait until it is funded before they can cancel.
							return Err(Error::<T, I>::UnexpectedStatus.into())
						},
						BountyStatus::Funded | BountyStatus::CuratorProposed { .. } => {
							// Nothing extra to do besides the refund payment below.
						},
						BountyStatus::Active { curator, .. } => {
							// Tiago: I should only unreserve once payment succeeds right?
							// Cancelled by council, refund deposit of the working curator.
							let err_amount =
								T::Currency::unreserve(curator, bounty.curator_deposit);
							debug_assert!(err_amount.is_zero());
							// Then execute refund payment below.
						},
						BountyStatus::PendingPayout { .. } |
						BountyStatus::PayoutAttempted { .. } => {
							// Bounty is already pending payout. If council wants to cancel
							// this bounty, it should mean the curator was acting maliciously.
							// So the council should first unassign the curator, slashing their
							// deposit.
							return Err(Error::<T, I>::PendingPayout.into())
						},
						BountyStatus::RefundAttempted { .. } => {
							// Bounty refund is already attempted. Flow should be
							// finished with calling `check_payment_status`
							// or retrying payment with `process_payment`
							// if it failed
							return Err(Error::<T, I>::PendingPayout.into())
						},
					}

					let treasury_account = Self::account_id();
					let bounty_account = Self::bounty_account_id(bounty_id);
					let payment_id = T::Paymaster::pay(
						&bounty_account,
						&treasury_account,
						bounty.asset_kind.clone(),
						bounty.value,
					)
					.map_err(|_| Error::<T, I>::RefundError)?;
					bounty.status = BountyStatus::RefundAttempted {
						payment_status: PaymentState::Attempted { id: payment_id },
					};

					Ok(Some(<T as Config<I>>::WeightInfo::close_bounty_active()).into())
				},
			)
		}

		/// Extend the expiry time of an active bounty.
		///
		/// ## Dispatch Origin
		/// Must be signed by the curator of the bounty.
		///
		/// ## Details
		/// - The bounty must be in the `Active` state.
		/// - Only the assigned curator can call this function.
		/// - The expiry time is extended by `T::BountyUpdatePeriod`, ensuring it does not decrease.
		/// - This function does not modify any other bounty properties.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty to extend.
		/// - `remark`: Additional information about the extension (not stored).
		///
		/// ## Events
		/// - Emits `BountyExtended` when the expiry time is successfully updated.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(8)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::extend_bounty_expiry())]
		pub fn extend_bounty_expiry(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
			_remark: Vec<u8>,
		) -> DispatchResult {
			let signer = ensure_signed(origin)?;

			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

				match bounty.status {
					BountyStatus::Active { ref curator, ref mut update_due, .. } => {
						ensure!(*curator == signer, Error::<T, I>::RequireCurator);
						*update_due = (Self::treasury_block_number() +
							T::BountyUpdatePeriod::get())
						.max(*update_due);
					},
					_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
				}

				Ok(())
			})?;

			Self::deposit_event(Event::<T, I>::BountyExtended { index: bounty_id });
			Ok(())
		}

		/// Approve a bounty and propose a curator simultaneously.
		/// This call is a shortcut to calling `approve_bounty` and `propose_curator` separately.
		///
		/// ## Dispatch Origin
		/// Must be called by `T::SpendOrigin`.
		///
		/// ## Details
		/// - This function combines the logic of `approve_bounty` and `propose_curator` into a
		///   single call.
		/// - The bounty must be in the `Proposed` state.
		/// - The `fee` must be lower than the bounty value.
		/// - The treasury must have sufficient funds to approve the bounty.
		/// - If successful, funds are transferred from the treasury to the bounty account.
		///
		/// ### Parameters
		/// - `bounty_id`: The index of the bounty to approve.
		/// - `curator`: The account of the curator who will manage the bounty.
		/// - `fee`: The fee that the curator will receive upon successful claim.
		///
		/// ## Events
		/// - Emits `BountyApproved` when the bounty is successfully approved.
		/// - Emits `CuratorProposed` when the curator is assigned.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(9)]
		#[pallet::weight(<T as Config<I>>::WeightInfo::approve_bounty_with_curator())]
		pub fn approve_bounty_with_curator(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
			curator: AccountIdLookupOf<T>,
			#[pallet::compact] fee: BountyBalanceOf<T, I>,
		) -> DispatchResult {
			let max_amount = T::SpendOrigin::ensure_origin(origin)?;
			let curator = T::Lookup::lookup(curator)?;
			Bounties::<T, I>::try_mutate_exists(bounty_id, |maybe_bounty| -> DispatchResult {
				// approve bounty
				let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;
				let native_amount =
					<T as pallet_treasury::Config<I>>::BalanceConverter::from_asset_balance(
						bounty.value,
						bounty.asset_kind.clone(),
					)
					.map_err(|_| pallet_treasury::Error::<T, I>::FailedToConvertBalance)?;
				ensure!(
					native_amount <= max_amount,
					pallet_treasury::Error::<T, I>::InsufficientPermission
				);
				ensure!(bounty.status == BountyStatus::Proposed, Error::<T, I>::UnexpectedStatus);
				ensure!(fee < bounty.value, Error::<T, I>::InvalidFee);

				// Tiago: is this the best way to use the SpendContext?
				with_context::<SpendContext<DepositBalanceOf<T, I>>, _>(|v| {
					let context = v.or_default();
					let spend = context.spend_in_context.entry(max_amount).or_default();

					if spend.checked_add(&native_amount).map(|s| s > max_amount).unwrap_or(true) {
						Err(pallet_treasury::Error::<T, I>::InsufficientPermission)
					} else {
						*spend = spend.saturating_add(native_amount);
						Ok(())
					}
				})
				.unwrap_or(Ok(()))?;

				let bounty_account = Self::bounty_account_id(bounty_id);
				let treasury_account = Self::account_id();
				let payment_id = T::Paymaster::pay(
					&treasury_account,
					&bounty_account,
					bounty.asset_kind.clone(),
					bounty.value,
				)
				.map_err(|_| Error::<T, I>::FundingError)?;

				bounty.status = BountyStatus::ApprovedWithCurator {
					curator: curator.clone(),
					payment_status: PaymentState::Attempted { id: payment_id },
				};
				bounty.fee = fee;

				Ok(())
			})?;

			Self::deposit_event(Event::<T, I>::BountyApproved { index: bounty_id });
			Self::deposit_event(Event::<T, I>::CuratorProposed { bounty_id, curator });

			Ok(())
		}

		/// Retry a payment for funding or closing a bounty.
		///
		/// ## Dispatch Origin
		/// Must be signed.
		///
		/// ## Details
		/// - If the bounty is in the `Approved` or `ApprovedWithCurator` state, it retries funding payment.
		/// - If the bounty is in the `PayoutAttempted` state, it retries the curator and
		///   beneficiary payouts.
		/// - If the bounty is in the `RefundAttempted` state, it retries the refund payment to return funds to the
		///   treasury.
		/// - `check_payment_status` must be called to advance bounty status.
		///
		/// ### Parameters
		/// - `bounty_id`: The bounty index.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(10)]
		// TODO: change weight
		#[pallet::weight(<T as Config<I>>::WeightInfo::approve_bounty_with_curator())]
		pub fn process_payment(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;

			Bounties::<T, I>::try_mutate_exists(
				bounty_id,
				|maybe_bounty| -> DispatchResultWithPostInfo {
					let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;

					match bounty.status {
						BountyStatus::Approved { ref mut payment_status } |
						BountyStatus::ApprovedWithCurator { ref mut payment_status, .. } => {
							ensure!(
								matches!(
									payment_status,
									PaymentState::Failed | PaymentState::Pending
								),
								Error::<T, I>::UnexpectedStatus
							);

							let treasury_account = Self::account_id();
							let bounty_account = Self::bounty_account_id(bounty_id);
							let id = T::Paymaster::pay(
								&treasury_account,
								&bounty_account,
								bounty.asset_kind.clone(),
								bounty.value,
							)
							.map_err(|_| Error::<T, I>::FundingError)?;

							*payment_status = PaymentState::Attempted { id };
							// Tiago: should I be returning something like
							// <T as Config<I>>::WeightInfo::process_payment_approved() in each arm?
							Ok(Pays::Yes.into())
						},
						BountyStatus::RefundAttempted { ref mut payment_status } => {
							ensure!(
								matches!(
									payment_status,
									PaymentState::Failed | PaymentState::Pending
								),
								Error::<T, I>::UnexpectedStatus
							);

							let bounty_account = Self::bounty_account_id(bounty_id);
							let treasury_account = Self::account_id();
							let id = T::Paymaster::pay(
								&bounty_account,
								&treasury_account,
								bounty.asset_kind.clone(),
								bounty.value,
							)
							.map_err(|_| Error::<T, I>::RefundError)?;

							*payment_status = PaymentState::Attempted { id };
							Ok(Pays::Yes.into())
						},
						BountyStatus::PayoutAttempted {
							ref mut curator_stash,
							ref mut beneficiary,
							..
						} => {
							let (final_fee, payout) = Self::calculate_curator_fee_and_payout(
								bounty_id,
								bounty.fee,
								bounty.value,
							);
							let bounty_account = Self::bounty_account_id(bounty_id);

							let statuses = [
								T::Paymaster::pay(
									&bounty_account,
									&curator_stash.0,
									bounty.asset_kind.clone(),
									final_fee,
								)
								.map_err(|_| Error::<T, I>::PayoutError),
								T::Paymaster::pay(
									&bounty_account,
									&beneficiary.0,
									bounty.asset_kind.clone(),
									payout,
								)
								.map_err(|_| Error::<T, I>::PayoutError),
							];
							// Tiago: process_payment does not change bounty.status state. Should it
							// change?

							let succeeded = statuses.iter().filter(|i| i.is_ok()).count();
							if succeeded > 0 {
								Ok(Pays::Yes.into())
							} else {
								Err(Error::<T, I>::PayoutError.into())
							}
						},
						_ => Err(Error::<T, I>::UnexpectedStatus.into()),
					}
				},
			)
		}

		/// Check and update the payment status of a bounty.
		///
		/// ## Dispatch Origin
		/// Must be signed.
		///
		/// ## Details
		/// - If the bounty is in the `Approved` or `ApprovedWithCurator` state, it checks if the
		///   funding payment has succeeded. If successful, the bounty becomes `Active`, and the
		///   proposer's deposit is unreserved.
		/// - If the bounty is in the `PayoutAttempted` state, it checks the status of curator and
		///   beneficiary payouts. If both payments succeed, the bounty is removed, and the
		///   curator's deposit is unreserved. If any payment failed, the bounty status is updated.
		/// - If the bounty is in the `RefundAttempted` state, it checks if the refund was
		///   completed. If successful, the bounty is removed.
		/// - If no progress is made in the state machine, an error is returned.
		///
		/// ### Parameters
		/// - `bounty_id`: The bounty index.
		///
		/// ## Events
		/// - Emits `BountyBecameActive` when the bounty transitions to `Active`.
		/// - Emits `BountyClaimed` when the payout process completes successfully.
		/// - Emits `BountyCanceled` if the refund is successful.
		///
		/// ## Complexity
		/// - O(1).
		#[pallet::call_index(11)]
		// TODO: change weight
		#[pallet::weight(<T as Config<I>>::WeightInfo::approve_bounty_with_curator())]
		pub fn check_payment_status(
			origin: OriginFor<T>,
			#[pallet::compact] bounty_id: BountyIndex,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;

			Bounties::<T, I>::try_mutate_exists(
				bounty_id,
				|maybe_bounty| -> DispatchResultWithPostInfo {
					let bounty = maybe_bounty.as_mut().ok_or(Error::<T, I>::InvalidIndex)?;
					let mut new_bounty_status = None;

					let result = match bounty.status {
						BountyStatus::Approved { ref mut payment_status } => match payment_status {
							PaymentState::Attempted { id } =>
								match T::Paymaster::check_payment(*id) {
									PaymentStatus::Success => {
										*payment_status = PaymentState::Succeeded;
										new_bounty_status = Some(BountyStatus::Funded);
										let err_amount =
											T::Currency::unreserve(&bounty.proposer, bounty.bond);
										debug_assert!(err_amount.is_zero());
										Self::deposit_event(Event::<T, I>::BountyBecameActive {
											index: bounty_id,
										});
										// Tiago: should I be returning something like
										// <T as Config<I>>::WeightInfo::check_payment_status_approved() in each arm?
										Ok(Pays::No.into())
									},
									PaymentStatus::InProgress =>
										return Err(Error::<T, I>::FundingInconclusive.into()),
									PaymentStatus::Unknown | PaymentStatus::Failure => {
										// TODO: should we assume payment has failed on unknown? not
										// sure yet
										*payment_status = PaymentState::Failed;
										// user can retry from this tate
										return Ok(Pays::No.into());
									},
								},
							_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
						},
						BountyStatus::ApprovedWithCurator {
							ref mut payment_status,
							ref curator,
						} => match payment_status {
							PaymentState::Attempted { id } =>
								match T::Paymaster::check_payment(*id) {
									PaymentStatus::Success => {
										*payment_status = PaymentState::Succeeded;
										new_bounty_status = Some(BountyStatus::CuratorProposed {
											curator: curator.clone(),
										});
										let err_amount =
											T::Currency::unreserve(&bounty.proposer, bounty.bond);
										debug_assert!(err_amount.is_zero());
										Self::deposit_event(Event::<T, I>::BountyBecameActive {
											index: bounty_id,
										});
										Ok(Pays::No.into())
									},
									PaymentStatus::InProgress =>
										return Err(Error::<T, I>::FundingInconclusive.into()),
									PaymentStatus::Unknown | PaymentStatus::Failure => {
										// TODO: should we assume payment has failed on unknown? not
										// sure yet
										*payment_status = PaymentState::Failed;
										// user can retry from this tate
										return Ok(Pays::No.into());
									},
								},
							_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
						},
						BountyStatus::PayoutAttempted {
							ref curator,
							ref mut curator_stash,
							ref mut beneficiary,
						} => {
							let (mut payments_progressed, mut payments_succeeded) = (0, 0);
							// advance both curator, and beneficiary payments
							for (account, payment_state) in [
								(&curator_stash.0, &mut curator_stash.1),
								(&beneficiary.0, &mut beneficiary.1),
							] {
								match payment_state {
									PaymentState::Attempted { id } =>
										match T::Paymaster::check_payment(*id) {
											PaymentStatus::Success => {
												*payment_state = PaymentState::Succeeded;
												payments_succeeded += 1;
												payments_progressed += 1;
											},
											PaymentStatus::InProgress => {
												// nothing new to report, return function without
												// error so we could drive the next
												// payment
											},
											PaymentStatus::Unknown | PaymentStatus::Failure => {
												payments_progressed += 1;
												*payment_state = PaymentState::Failed;
											},
										},
									PaymentState::Succeeded => {
										payments_succeeded += 1;
									},
									_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
								}
							}

							// best scenario, both payments have succeeded,
							// emit events and advance state machine to the end
							if payments_succeeded >= 2 {
								// all payments succeeded, cleanup the bounty
								let (_final_fee, payout) = Self::calculate_curator_fee_and_payout(
									bounty_id,
									bounty.fee,
									bounty.value,
								);

								// Tiago: Should I remove the bounty since it was being removed in
								// claim_bounty
								Bounties::<T, I>::remove(bounty_id);
								BountyDescriptions::<T, I>::remove(bounty_id);
								T::ChildBountyManager::bounty_removed(bounty_id);
								// Tiago: Unreserve here?
								// Unreserve the curator deposit when payment succeeds
								let err_amount =
									T::Currency::unreserve(&curator, bounty.curator_deposit);
								debug_assert!(err_amount.is_zero()); // Ensure nothing remains reserved
								Self::deposit_event(Event::<T, I>::BountyClaimed {
									index: bounty_id,
									asset_kind: bounty.asset_kind.clone(),
									asset_payout: payout,
									beneficiary: beneficiary.0.clone(),
								});
								*maybe_bounty = None;
								return Ok(Pays::No.into());
							} else if payments_progressed > 0 {
								// some payments have progressed in the state machine
								// return ok so these changes are saved to the state
								Ok(Pays::Yes.into())
							} else {
								// no progress was made in the state machine if we're here,
								return Err(Error::<T, I>::PayoutInconclusive.into());
							}
						},
						BountyStatus::RefundAttempted { ref mut payment_status } => {
							match payment_status {
								PaymentState::Attempted { id } =>
									match T::Paymaster::check_payment(*id) {
										PaymentStatus::Success => {
											// Tiago: Do we need this?
											// let res = T::Currency::transfer(
											// 	&bounty_account,
											// 	&Self::account_id(),
											// 	balance,
											// 	AllowDeath,
											// ); // should not fail
											// debug_assert!(res.is_ok());

											// refund succeeded, cleanup the bounty
											BountyDescriptions::<T, I>::remove(bounty_id);
											T::ChildBountyManager::bounty_removed(bounty_id);
											*maybe_bounty = None;
											Self::deposit_event(Event::<T, I>::BountyCanceled {
												index: bounty_id,
											});
											return Ok(Pays::No.into());
										},
										// nothing new to report
										PaymentStatus::InProgress =>
											return Err(Error::<T, I>::RefundInconclusive.into()),
										PaymentStatus::Unknown | PaymentStatus::Failure => {
											// assume payment has failed, allow user to retry
											*payment_status = PaymentState::Failed;
											return Ok(Pays::Yes.into());
										},
									},
								// `Pending` and `Failed` states should trigger user to call
								// `process_payment` retry. `Succeeded` should never be
								// reached since a successful refund would have
								//   already removed the bounty from storage.
								_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
							}
						},
						_ => return Err(Error::<T, I>::UnexpectedStatus.into()),
					};

					// set bounty status only now to satisfy ownership rules
					if let Some(new_status) = new_bounty_status {
						bounty.status = new_status;
					}

					result
				},
			)
		}
	}

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<SystemBlockNumberFor<T>> for Pallet<T, I> {
		#[cfg(feature = "try-runtime")]
		fn try_state(_n: SystemBlockNumberFor<T>) -> Result<(), sp_runtime::TryRuntimeError> {
			Self::do_try_state()
		}
	}
}

#[cfg(any(feature = "try-runtime", test))]
impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Ensure the correctness of the state of this pallet.
	///
	/// This should be valid before or after each state transition of this pallet.
	pub fn do_try_state() -> Result<(), sp_runtime::TryRuntimeError> {
		Self::try_state_bounties_count()?;

		Ok(())
	}

	/// # Invariants
	///
	/// * `BountyCount` should be greater or equals to the length of the number of items in
	///   `Bounties`.
	/// * `BountyCount` should be greater or equals to the length of the number of items in
	///   `BountyDescriptions`.
	/// * Number of items in `Bounties` should be the same as `BountyDescriptions` length.
	fn try_state_bounties_count() -> Result<(), sp_runtime::TryRuntimeError> {
		let bounties_length = Bounties::<T, I>::iter().count() as u32;

		ensure!(
			<BountyCount<T, I>>::get() >= bounties_length,
			"`BountyCount` must be grater or equals the number of `Bounties` in storage"
		);

		let bounties_description_length = BountyDescriptions::<T, I>::iter().count() as u32;
		ensure!(
			<BountyCount<T, I>>::get() >= bounties_description_length,
			"`BountyCount` must be grater or equals the number of `BountiesDescriptions` in storage."
		);

		ensure!(
				bounties_length == bounties_description_length,
				"Number of `Bounties` in storage must be the same as the Number of `BountiesDescription` in storage."
		);
		Ok(())
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Get the block number used in the treasury pallet.
	///
	/// It may be configured to use the relay chain block number on a parachain.
	pub fn treasury_block_number() -> BlockNumberFor<T, I> {
		<T as pallet_treasury::Config<I>>::BlockNumberProvider::current_block_number()
	}

	/// Calculate the deposit required for a curator.
	pub fn calculate_curator_deposit(
		fee: &BountyBalanceOf<T, I>,
		asset_kind: T::AssetKind,
	) -> Result<DepositBalanceOf<T, I>, pallet_treasury::Error<T, I>> {
		let fee = <T as pallet_treasury::Config<I>>::BalanceConverter::from_asset_balance(
			*fee, asset_kind,
		)
		.map_err(|_| pallet_treasury::Error::<T, I>::FailedToConvertBalance)?;

		let mut deposit = T::CuratorDepositMultiplier::get() * fee;

		if let Some(max_deposit) = T::CuratorDepositMax::get() {
			deposit = deposit.min(max_deposit)
		}

		if let Some(min_deposit) = T::CuratorDepositMin::get() {
			deposit = deposit.max(min_deposit)
		}

		Ok(deposit)
	}

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::Beneficiary {
		T::PalletId::get().into_account_truncating()
	}

	/// The account ID of a bounty account
	pub fn bounty_account_id(id: BountyIndex) -> T::Beneficiary {
		// only use two byte prefix to support 16 byte account id (used by test)
		// "modl" ++ "py/trsry" ++ "bt" is 14 bytes, and two bytes remaining for bounty index
		T::PalletId::get().into_sub_account_truncating(("bt", id))
	}

	/// Return the amount of money in the bounty.
	pub fn bounty_balance(id: BountyIndex) -> DepositBalanceOf<T, I> {
		// Tiago: Currency::free_balance accepts AccountId. Is this how I can get the balance of the
		// bounty?
		let native_account_id = T::PalletId::get().into_sub_account_truncating(("bt", id));
		T::Currency::free_balance(&native_account_id)
			// Must never be less than 0 but better be safe.
			.saturating_sub(T::Currency::minimum_balance())
	}

	fn create_bounty(
		proposer: T::AccountId,
		description: Vec<u8>,
		asset_kind: T::AssetKind,
		value: BountyBalanceOf<T, I>,
	) -> DispatchResult {
		let bounded_description: BoundedVec<_, _> =
			description.try_into().map_err(|_| Error::<T, I>::ReasonTooBig)?;
		let native_amount =
			<T as pallet_treasury::Config<I>>::BalanceConverter::from_asset_balance(
				value,
				asset_kind.clone(),
			)
			.map_err(|_| pallet_treasury::Error::<T, I>::FailedToConvertBalance)?;

		ensure!(native_amount >= T::BountyValueMinimum::get(), Error::<T, I>::InvalidValue);

		let index = BountyCount::<T, I>::get();

		// reserve deposit for new bounty
		let bond = T::BountyDepositBase::get() +
			T::DataDepositPerByte::get() * (bounded_description.len() as u32).into();
		T::Currency::reserve(&proposer, bond)
			.map_err(|_| Error::<T, I>::InsufficientProposersBalance)?;

		BountyCount::<T, I>::put(index + 1);

		let bounty = BountyOf::<T, I> {
			proposer,
			asset_kind,
			value,
			fee: 0u32.into(),
			curator_deposit: 0u32.into(),
			bond,
			status: BountyStatus::Proposed,
		};

		Bounties::<T, I>::insert(index, &bounty);
		BountyDescriptions::<T, I>::insert(index, bounded_description);

		Self::deposit_event(Event::<T, I>::BountyProposed { index });

		Ok(())
	}

	fn calculate_curator_fee_and_payout(
		bounty_id: BountyIndex,
		fee: BountyBalanceOf<T, I>,
		value: BountyBalanceOf<T, I>,
	) -> (BountyBalanceOf<T, I>, BountyBalanceOf<T, I>) {
		// Tiago: The payout should be the balance of the bounty account of asset_kind.
		// if a child bounty is added and claimed, and parent-bounty is claimed the bounty.amount is
		// returned and not the balance of the bounty account.
		// right? how to handle this?
		let payout = value - fee;

		// Get total child bounties curator fees, and subtract it from the parent
		// curator fee (the fee in present referenced bounty, `self`).
		let children_fee = T::ChildBountyManager::children_curator_fees(bounty_id);
		debug_assert!(children_fee <= fee);

		let final_fee = fee.saturating_sub(children_fee);
		(final_fee, payout)
	}
}

// Default impl for when ChildBounties is not being used in the runtime.
impl<Balance: Zero> ChildBountyManager<Balance> for () {
	fn child_bounties_count(_bounty_id: BountyIndex) -> BountyIndex {
		Default::default()
	}

	fn children_curator_fees(_bounty_id: BountyIndex) -> Balance {
		Zero::zero()
	}

	fn bounty_removed(_bounty_id: BountyIndex) {}
}
