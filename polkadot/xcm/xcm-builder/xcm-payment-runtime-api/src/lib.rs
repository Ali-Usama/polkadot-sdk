// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Runtime API definition for xcm transaction payment.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Codec;
use sp_std::vec::Vec;
use sp_weights::Weight;
use xcm::latest::{AssetId, Xcm};
sp_api::decl_runtime_apis! {
	/// A trait of XCM payment API.
	///
	/// API provides functionality for obtaining
	/// the weight required to execute an XCM message,
	/// a list of accepted `AssetId` for payment for its
	/// execution and the cost in the specified supported `AssetId`.
	///
	/// To determine the execution weight of the calls required
	/// for some instructions (for example, [`xcm::latest::Instruction::Transact`])
	/// `TransactionPaymentCallApi`can be used.
	pub trait XcmPaymentRuntimeApi<Call>
	where
		Call: Codec,
	{
		/// Returns a list of acceptable payment assets.
		fn query_acceptable_payment_assets() -> Vec<AssetId>;

		/// Converts a weight into a fee for the specified `AssetId`.
		/// Returns `None` if the `AssetId` isn't supported as a acceptable for the fee payment.
		///
		/// # Arguments
		///
		/// * `weight`: convertible `Weight`.
		/// * `asset`: `AssetId`.
		fn query_weight_to_asset_fee(weight: Weight, asset: AssetId) -> Option<u128>;

		/// Returns a weight needed to execute a XCM.
		///
		/// # Arguments
		///
		/// * `message`: `Xcm`.
		fn query_xcm_weight(message: Xcm<Call>) -> Result<Weight, Xcm<Call>>;
	}
}
