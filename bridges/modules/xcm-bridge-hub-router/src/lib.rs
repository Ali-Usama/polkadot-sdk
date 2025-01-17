// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Parity Bridges Common.

// Parity Bridges Common is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity Bridges Common is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity Bridges Common.  If not, see <http://www.gnu.org/licenses/>.

//! A pallet that can be used as an alternative in the XCM router configuration — see the `SendXcm`
//! implementation for details.
//!
//! ## Features
//!
//! This pallet offers several optional features to customize functionality:
//!
//! ### Message Size Fee
//! An optional fee based on `T::FeeAsset` and `T::ByteFee`. If `T::FeeAsset` is not specified, this
//! fee is not calculated.
//!
//! ### Dynamic Fees and Congestion
//!
//! This pallet supports storing the congestion status of bridge outbound queues. The fee increases
//! exponentially if the queue between this chain and a sibling or child bridge hub becomes
//! congested. All other bridge hub queues provide backpressure mechanisms, so if any of these
//! queues are congested, it will eventually lead to increased queuing on this chain.
//!
//! There are two methods for storing congestion status:
//! 1. A dedicated extrinsic `update_bridge_status`, which relies on `T::BridgeHubOrigin`. This
//!    allows the message exporter to send, for example, an XCM `Transact`.
//! 2. An implementation of `bp_xcm_bridge_hub::LocalXcmChannelManager`.
//!
//! ## Usage
//!
//! This pallet provides several implementations, such as `ViaLocalBridgeHubExporter` and
//! `ViaRemoteBridgeHubExporter`, which can expose or access these features.
//!
//! This router can be used in two main scenarios, depending on where the router and message
//! exporter (e.g., `pallet_xcm_bridge_hub` or another pallet with an `ExportXcm` implementation)
//! are deployed:
//!
//! ### On the Same Chain as the Message Exporter
//! In this setup, the router directly calls an `ExportXcm` implementation. In this case,
//! `ViaLocalBridgeHubExporter` can be used as a wrapper with `T::MessageExporter`.
//!
//! ### On a Different Chain than the Message Exporter
//! In this setup, we need to provide a `SendXcm` implementation for `T::MessageExporter`, which
//! sends `ExportMessage`. For example, `SovereignPaidRemoteExporter` can be used with
//! `ViaRemoteBridgeHubExporter`.
//!
//! **Note on Terminology**: When we refer to the bridge hub, we mean the chain that has the
//! `pallet-bridge-messages` with an `ExportXcm` implementation deployed, such as
//! `pallet-xcm-bridge-hub`. Depending on the deployment setup, `T::MessageExporter` can be
//! configured accordingly — see `T::MessageExporter` for additional documentation.

#![cfg_attr(not(feature = "std"), no_std)]

pub use bp_xcm_bridge_hub_router::{BridgeState, ResolveBridgeId};
use codec::Encode;
use frame_support::traits::{EnsureOriginWithArg, Get};
use sp_runtime::{FixedPointNumber, FixedU128, Saturating};
use sp_std::vec::Vec;
use xcm::prelude::*;
use xcm_builder::InspectMessageQueues;

pub use pallet::*;
pub use weights::WeightInfo;

pub mod benchmarking;
pub mod impls;
pub mod weights;

mod mock;

/// Minimal delivery fee factor.
pub const MINIMAL_DELIVERY_FEE_FACTOR: FixedU128 = FixedU128::from_u32(1);

/// The factor that is used to increase current message fee factor when bridge experiencing
/// some lags.
const EXPONENTIAL_FEE_BASE: FixedU128 = FixedU128::from_rational(105, 100); // 1.05
/// The factor that is used to increase current message fee factor for every sent kilobyte.
const MESSAGE_SIZE_FEE_BASE: FixedU128 = FixedU128::from_rational(1, 1000); // 0.001

/// Maximal size of the XCM message that may be sent over bridge.
///
/// This should be less than the maximal size, allowed by the messages pallet, because
/// the message itself is wrapped in other structs and is double encoded.
pub const HARD_MESSAGE_SIZE_LIMIT: u32 = 32 * 1024;

/// The target that will be used when publishing logs related to this pallet.
pub const LOG_TARGET: &str = "xcm::bridge-router";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// Default implementations of [`DefaultConfig`], which can be used to implement [`Config`].
	pub mod config_preludes {
		use super::*;
		use frame_support::{derive_impl, traits::ConstU128};

		/// A type providing default configurations for this pallet in testing environment.
		pub struct TestDefaultConfig;

		#[derive_impl(frame_system::config_preludes::TestDefaultConfig, no_aggregated_types)]
		impl frame_system::DefaultConfig for TestDefaultConfig {}

		#[frame_support::register_default_impl(TestDefaultConfig)]
		impl DefaultConfig for TestDefaultConfig {
			#[inject_runtime_type]
			type RuntimeEvent = ();
			type WeightInfo = ();
			type DestinationVersion = AlwaysLatest;

			// We don't need (optional) message_size fees.
			type ByteFee = ConstU128<0>;
			// We don't need (optional) message_size fees.
			type FeeAsset = ();
		}
	}

	#[pallet::config(with_default)]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		#[pallet::no_default_bounds]
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// Benchmarks results from runtime we're plugged into.
		type WeightInfo: WeightInfo;

		/// Checks the XCM version for the destination.
		type DestinationVersion: GetVersion;

		/// The bridge hub may be:
		/// - A system (sibling) bridge hub parachain (or another chain), in which case we need an
		///   implementation for `T::MessageExporter` that sends `ExportMessage`, e.g.,
		///   `SovereignPaidRemoteExporter`.
		/// - The local chain, in which case we need an implementation for `T::MessageExporter`
		///   that does not use `ExportMessage` but instead directly calls the `ExportXcm`
		///   implementation.
		#[pallet::no_default]
		type MessageExporter: SendXcm;

		/// Resolves a specific `BridgeId` for `dest`, used for identifying the bridge in cases of
		/// congestion and dynamic fees. If it resolves to `None`, it means no congestion or
		/// dynamic fees are handled for `dest`.
		#[pallet::no_default]
		type BridgeIdResolver: ResolveBridgeId;

		/// Origin of the sibling bridge hub that is allowed to update bridge status.
		#[pallet::no_default]
		type BridgeHubOrigin: EnsureOriginWithArg<Self::RuntimeOrigin, BridgeIdOf<Self, I>>;

		/// Additional fee that is paid for every byte of the outbound message.
		/// See `calculate_message_size_fee` for more details.
		type ByteFee: Get<u128>;
		/// Asset used to pay the `ByteFee`.
		/// If not specified, the `ByteFee` is ignored.
		/// See `calculate_fees` for more details.
		type FeeAsset: Get<Option<AssetId>>;
	}

	/// An alias for the `BridgeId` of configured `T::BridgeIdResolver`.
	pub type BridgeIdOf<T, I> = <<T as Config<I>>::BridgeIdResolver as ResolveBridgeId>::BridgeId;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Notification about congested bridge queue.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::update_bridge_status())]
		pub fn update_bridge_status(
			origin: OriginFor<T>,
			bridge_id: BridgeIdOf<T, I>,
			is_congested: bool,
		) -> DispatchResult {
			let _ = T::BridgeHubOrigin::ensure_origin(origin, &bridge_id)?;

			log::info!(
				target: LOG_TARGET,
				"Received bridge status from {:?}: congested = {}",
				bridge_id,
				is_congested,
			);

			// update status
			Self::do_update_bridge_status(bridge_id, is_congested);

			Ok(())
		}
	}

	/// Stores `BridgeState` for congestion control and dynamic fees for each resolved bridge ID
	/// associated with a destination.
	#[pallet::storage]
	pub type Bridges<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, BridgeIdOf<T, I>, BridgeState, OptionQuery>;

	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Called when new message is sent to the `dest` (queued to local outbound XCM queue).
		pub(crate) fn on_message_sent_to(message_size: u32, dest: Location) {
			let Some(bridge_id) = T::BridgeIdResolver::resolve_for_dest(&dest) else {
				// not supported bridge id, so do nothing
				return
			};

			// handle congestion and fee factor (if detected)
			Bridges::<T, I>::mutate_exists(&bridge_id, |bridge_state| match bridge_state {
				Some(ref mut bridge_state) if bridge_state.is_congested => {
					// found congested bridge
					// ok - we need to increase the fee factor, let's do that
					let message_size_factor =
						FixedU128::from_u32(message_size.saturating_div(1024))
							.saturating_mul(MESSAGE_SIZE_FEE_BASE);
					let total_factor = EXPONENTIAL_FEE_BASE.saturating_add(message_size_factor);

					let previous_factor = bridge_state.delivery_fee_factor;
					bridge_state.delivery_fee_factor =
						bridge_state.delivery_fee_factor.saturating_mul(total_factor);

					log::info!(
						target: LOG_TARGET,
						"Bridge channel with id {:?} is congested. Increased fee factor from {} to {} for {:?}",
						bridge_id,
						previous_factor,
						bridge_state.delivery_fee_factor,
						dest
					);
					Self::deposit_event(Event::DeliveryFeeFactorIncreased {
						previous_value: previous_factor,
						new_value: bridge_state.delivery_fee_factor,
						bridge_id: bridge_id.clone(),
					});
				},
				_ => {
					// not congested, do nothing
				},
			});
		}

		/// Returns the recalculated dynamic fee for a given asset based on the bridge state.
		///
		/// This function adjusts the amount of a fungible asset according to the delivery fee
		/// factor specified in the `bridge_state`. If the asset is fungible, the
		/// `delivery_fee_factor` is applied to the asset’s amount, potentially altering its
		/// value.
		pub(crate) fn calculate_dynamic_fee(bridge_state: &BridgeState, asset: Asset) -> Asset {
			match asset.fun {
				Fungible(amount) => {
					let adjusted_amount = bridge_state.delivery_fee_factor.saturating_mul_int(amount);
					Asset {
						fun: Fungible(adjusted_amount),
						..asset
					}
				}
				_ => asset,
			}
		}

		/// Calculates an (optional) fee for message size based on `T::ByteFee` and `T::FeeAsset`.
		pub(crate) fn calculate_message_size_fee(
			message_size: impl FnOnce() -> u32,
		) -> Option<Asset> {
			// Apply message size `T::ByteFee/T::FeeAsset` feature (if configured).
			if let Some(asset_id) = T::FeeAsset::get() {
				let message_fee = (message_size() as u128).saturating_mul(T::ByteFee::get());
				if message_fee > 0 {
					return Some((asset_id, message_fee).into());
				}
			}
			None
		}

		/// Updates the congestion status of a bridge for a given `bridge_id`.
		///
		/// If the bridge does not exist and:
		/// - `is_congested` is true, a new `BridgeState` is created with a default
		///   `delivery_fee_factor`.
		/// - `is_congested` is false, does nothing and no `BridgeState` is created.
		pub(crate) fn do_update_bridge_status(bridge_id: BridgeIdOf<T, I>, is_congested: bool) {
			Bridges::<T, I>::mutate_exists(&bridge_id, |maybe_bridge| match maybe_bridge.take() {
				Some(mut bridge) => if is_congested {
					bridge.is_congested = is_congested;
					*maybe_bridge = Some(bridge);
				} else {
					Self::deposit_event(Event::DeliveryFeeFactorDecreased {
						previous_value: bridge.delivery_fee_factor,
						new_value: 0.into(),
						bridge_id: bridge_id.clone(),
					});
				},
				None =>
					if is_congested {
						*maybe_bridge = Some(BridgeState {
							delivery_fee_factor: MINIMAL_DELIVERY_FEE_FACTOR,
							is_congested,
						});

						Self::deposit_event(Event::DeliveryFeeFactorIncreased {
							previous_value: 0.into(),
							new_value: MINIMAL_DELIVERY_FEE_FACTOR,
							bridge_id: bridge_id.clone(),
						});
					},
			});
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// Delivery fee factor has been decreased.
		DeliveryFeeFactorDecreased {
			/// Previous value of the `DeliveryFeeFactor`.
			previous_value: FixedU128,
			/// New value of the `DeliveryFeeFactor`.
			new_value: FixedU128,
			/// Bridge identifier.
			bridge_id: BridgeIdOf<T, I>,
		},
		/// Delivery fee factor has been increased.
		DeliveryFeeFactorIncreased {
			/// Previous value of the `DeliveryFeeFactor`.
			previous_value: FixedU128,
			/// New value of the `DeliveryFeeFactor`.
			new_value: FixedU128,
			/// Bridge identifier.
			bridge_id: BridgeIdOf<T, I>,
		},
	}
}

// This pallet acts as the `SendXcm` to the sibling/child bridge hub instead of regular
// XCMP/DMP transport. This allows injecting dynamic message fees into XCM programs that
// are going to the bridged network.
impl<T: Config<I>, I: 'static> SendXcm for Pallet<T, I> {
	type Ticket = (u32, Location, <T::MessageExporter as SendXcm>::Ticket);

	fn validate(
		dest: &mut Option<Location>,
		xcm: &mut Option<Xcm<()>>,
	) -> SendResult<Self::Ticket> {
		log::trace!(target: LOG_TARGET, "validate - msg: {xcm:?}, destination: {dest:?}");

		// In case of success, the `T::MessageExporter` can modify XCM instructions and consume
		// `dest` / `xcm`, so we retain the clone of original message and the destination for later
		// `DestinationVersion` validation.
		let xcm_to_dest_clone = xcm.clone();
		let dest_clone = dest.clone();

		// First, use the inner exporter to validate the destination to determine if it is even
		// routable. If it is not, return an error. If it is, then the XCM is extended with
		// instructions to pay the message fee at the sibling/child bridge hub. The cost will
		// include both the cost of (1) delivery to the sibling bridge hub (returned by
		// `Config::MessageExporter`) and (2) delivery to the bridged bridge hub (returned by
		// `Self::exporter_for`).
		match T::MessageExporter::validate(dest, xcm) {
			Ok((ticket, cost)) => {
				// If the ticket is ok, it means we are routing with this router, so we need to
				// apply more validations to the cloned `dest` and `xcm`, which are required here.
				let xcm_to_dest_clone = xcm_to_dest_clone.ok_or(SendError::MissingArgument)?;
				let dest_clone = dest_clone.ok_or(SendError::MissingArgument)?;

				// We won't have access to `dest` and `xcm` in the `deliver` method, so we need to
				// precompute everything required here. However, `dest` and `xcm` were consumed by
				// `T::MessageExporter`, so we need to use their clones.
				let message_size = xcm_to_dest_clone.encoded_size() as _;

				// The bridge doesn't support oversized or overweight messages. Therefore, it's
				// better to drop such messages here rather than at the bridge hub. Let's check the
				// message size.
				if message_size > HARD_MESSAGE_SIZE_LIMIT {
					return Err(SendError::ExceedsMaxMessageSize)
				}

				// We need to ensure that the known `dest`'s XCM version can comprehend the current
				// `xcm` program. This may seem like an additional, unnecessary check, but it is
				// not. A similar check is probably performed by the `T::MessageExporter`, which
				// attempts to send a versioned message to the sibling bridge hub. However, the
				// local bridge hub may have a higher XCM version than the remote `dest`. Once
				// again, it is better to discard such messages here than at the bridge hub (e.g.,
				// to avoid losing funds).
				let destination_version = T::DestinationVersion::get_version_for(&dest_clone)
					.ok_or(SendError::DestinationUnsupported)?;
				let _ = VersionedXcm::from(xcm_to_dest_clone)
					.into_version(destination_version)
					.map_err(|()| SendError::DestinationUnsupported)?;

				log::info!(
					target: LOG_TARGET,
					"Going to send message to {dest_clone:?} ({message_size:?} bytes) with actual cost: {cost:?}"
				);

				Ok(((message_size, dest_clone, ticket), cost))
			},
			Err(e) => {
				log::trace!(target: LOG_TARGET, "`T::MessageExporter` validates for dest: {dest_clone:?} with error: {e:?}");
				Err(e)
			},
		}
	}

	fn deliver(ticket: Self::Ticket) -> Result<XcmHash, SendError> {
		// use router to enqueue message to the sibling/child bridge hub. This also should handle
		// payment for passing through this queue.
		let (message_size, dest, ticket) = ticket;
		let xcm_hash = T::MessageExporter::deliver(ticket)?;

		log::trace!(
			target: LOG_TARGET,
			"deliver - message (size: {message_size:?}) sent to the dest: {dest:?}, xcm_hash: {xcm_hash:?}"
		);

		// increase delivery fee factor (if required)
		Self::on_message_sent_to(message_size, dest);

		Ok(xcm_hash)
	}
}

impl<T: Config<I>, I: 'static> InspectMessageQueues for Pallet<T, I> {
	fn clear_messages() {}

	/// This router needs to implement `InspectMessageQueues` but doesn't have to
	/// return any messages, since it just reuses the `XcmpQueue` router.
	fn get_messages() -> Vec<(VersionedLocation, Vec<VersionedXcm<()>>)> {
		Vec::new()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use frame_support::assert_ok;
	use mock::*;

	use frame_system::{EventRecord, Phase};
	use sp_runtime::traits::Dispatchable;

	#[test]
	fn not_applicable_if_destination_is_within_other_network() {
		run_test(|| {
			// unroutable dest
			let dest = Location::new(2, [GlobalConsensus(ByGenesis([0; 32])), Parachain(1000)]);
			let xcm: Xcm<()> = vec![ClearOrigin].into();

			// check that router does not consume when `NotApplicable`
			let mut xcm_wrapper = Some(xcm.clone());
			assert_eq!(
				XcmBridgeHubRouter::validate(&mut Some(dest.clone()), &mut xcm_wrapper),
				Err(SendError::NotApplicable),
			);
			// XCM is NOT consumed and untouched
			assert_eq!(Some(xcm.clone()), xcm_wrapper);

			// check the full `send_xcm`
			assert_eq!(send_xcm::<XcmBridgeHubRouter>(dest, xcm,), Err(SendError::NotApplicable),);
		});
	}

	#[test]
	fn exceeds_max_message_size_if_size_is_above_hard_limit() {
		run_test(|| {
			// routable dest with XCM version
			let dest =
				Location::new(2, [GlobalConsensus(BridgedNetworkId::get()), Parachain(1000)]);
			// oversized XCM
			let xcm: Xcm<()> = vec![ClearOrigin; HARD_MESSAGE_SIZE_LIMIT as usize].into();

			// dest is routable with the inner router
			assert_ok!(<TestRuntime as Config<()>>::MessageExporter::validate(
				&mut Some(dest.clone()),
				&mut Some(xcm.clone())
			));

			// check for oversized message
			let mut xcm_wrapper = Some(xcm.clone());
			assert_eq!(
				XcmBridgeHubRouter::validate(&mut Some(dest.clone()), &mut xcm_wrapper),
				Err(SendError::ExceedsMaxMessageSize),
			);
			// XCM is consumed by the inner router
			assert!(xcm_wrapper.is_none());

			// check the full `send_xcm`
			assert_eq!(
				send_xcm::<XcmBridgeHubRouter>(dest, xcm,),
				Err(SendError::ExceedsMaxMessageSize),
			);
		});
	}

	#[test]
	fn destination_unsupported_if_wrap_version_fails() {
		run_test(|| {
			// routable dest but we don't know XCM version
			let dest = UnknownXcmVersionForRoutableLocation::get();
			let xcm: Xcm<()> = vec![ClearOrigin].into();

			// dest is routable with the inner router
			assert_ok!(<TestRuntime as Config<()>>::MessageExporter::validate(
				&mut Some(dest.clone()),
				&mut Some(xcm.clone())
			));

			// check that it does not pass XCM version check
			let mut xcm_wrapper = Some(xcm.clone());
			assert_eq!(
				XcmBridgeHubRouter::validate(&mut Some(dest.clone()), &mut xcm_wrapper),
				Err(SendError::DestinationUnsupported),
			);
			// XCM is consumed by the inner router
			assert!(xcm_wrapper.is_none());

			// check the full `send_xcm`
			assert_eq!(
				send_xcm::<XcmBridgeHubRouter>(dest, xcm,),
				Err(SendError::DestinationUnsupported),
			);
		});
	}

	#[test]
	fn returns_proper_delivery_price() {
		run_test(|| {
			let dest = Location::new(2, [GlobalConsensus(BridgedNetworkId::get())]);
			let xcm: Xcm<()> = vec![ClearOrigin].into();
			let msg_size = xcm.encoded_size();

			// `BASE_FEE + BYTE_FEE * msg_size` (without `HRMP_FEE`)
			let base_cost_formula = || BASE_FEE + BYTE_FEE * (msg_size as u128);

			// initially the base fee is used
			let expected_fee = base_cost_formula() + HRMP_FEE;
			assert_eq!(
				XcmBridgeHubRouter::validate(&mut Some(dest.clone()), &mut Some(xcm.clone()))
					.unwrap()
					.1
					.get(0),
				Some(&(BridgeFeeAsset::get(), expected_fee).into()),
			);

			// but when factor is larger than one, it increases the fee, so it becomes:
			// `base_cost_formula() * F`
			let factor = FixedU128::from_rational(125, 100);

			// make bridge congested + update fee factor
			set_bridge_state_for::<TestRuntime, ()>(
				&dest,
				Some(BridgeState { delivery_fee_factor: factor, is_congested: true }),
			);

			let expected_fee =
				(FixedU128::saturating_from_integer(base_cost_formula()) * factor).into_inner() /
					FixedU128::DIV + HRMP_FEE;
			assert_eq!(
				XcmBridgeHubRouter::validate(&mut Some(dest), &mut Some(xcm)).unwrap().1.get(0),
				Some(&(BridgeFeeAsset::get(), expected_fee).into()),
			);
		});
	}

	#[test]
	fn sent_message_doesnt_increase_factor_if_bridge_is_uncongested() {
		run_test(|| {
			let dest =
				Location::new(2, [GlobalConsensus(BridgedNetworkId::get()), Parachain(1000)]);

			// make bridge congested + update fee factor
			let old_delivery_fee_factor = FixedU128::from_rational(125, 100);
			set_bridge_state_for::<TestRuntime, ()>(
				&dest,
				Some(BridgeState {
					delivery_fee_factor: old_delivery_fee_factor,
					is_congested: false,
				}),
			);

			assert_eq!(
				send_xcm::<XcmBridgeHubRouter>(dest.clone(), vec![ClearOrigin].into(),).map(drop),
				Ok(()),
			);

			assert!(TestXcmRouter::is_message_sent());
			assert_eq!(
				old_delivery_fee_factor,
				get_bridge_state_for::<TestRuntime, ()>(&dest).unwrap().delivery_fee_factor
			);

			assert_eq!(System::events(), vec![]);
		});
	}

	#[test]
	fn sent_message_increases_factor_if_bridge_is_congested() {
		run_test(|| {
			let dest =
				Location::new(2, [GlobalConsensus(BridgedNetworkId::get()), Parachain(1000)]);

			// make bridge congested + update fee factor
			let old_delivery_fee_factor = FixedU128::from_rational(125, 100);
			set_bridge_state_for::<TestRuntime, ()>(
				&dest,
				Some(BridgeState {
					delivery_fee_factor: old_delivery_fee_factor,
					is_congested: true,
				}),
			);

			assert_ok!(
				send_xcm::<XcmBridgeHubRouter>(dest.clone(), vec![ClearOrigin].into(),).map(drop)
			);

			assert!(TestXcmRouter::is_message_sent());
			assert!(
				old_delivery_fee_factor <
					get_bridge_state_for::<TestRuntime, ()>(&dest).unwrap().delivery_fee_factor
			);

			// check emitted event
			let first_system_event = System::events().first().cloned();
			assert!(matches!(
				first_system_event,
				Some(EventRecord {
					phase: Phase::Initialization,
					event: RuntimeEvent::XcmBridgeHubRouter(
						Event::DeliveryFeeFactorIncreased { .. }
					),
					..
				})
			));
		});
	}

	#[test]
	fn get_messages_does_not_return_anything() {
		run_test(|| {
			assert_ok!(send_xcm::<XcmBridgeHubRouter>(
				(Parent, Parent, GlobalConsensus(BridgedNetworkId::get()), Parachain(1000)).into(),
				vec![ClearOrigin].into()
			));
			assert_eq!(XcmBridgeHubRouter::get_messages(), vec![]);
		});
	}

	#[test]
	fn update_bridge_status_works() {
		run_test(|| {
			let dest =
				Location::new(2, [GlobalConsensus(BridgedNetworkId::get()), Parachain(1000)]);
			let bridge_id =
				bp_xcm_bridge_hub::BridgeId::new(&UniversalLocation::get(), dest.interior());
			let update_bridge_status = |bridge_id, is_congested| {
				let call = RuntimeCall::XcmBridgeHubRouter(Call::update_bridge_status {
					bridge_id,
					is_congested,
				});
				assert_ok!(call.dispatch(RuntimeOrigin::root()));
			};

			assert!(get_bridge_state_for::<TestRuntime, ()>(&dest).is_none());
			update_bridge_status(bridge_id, false);
			assert!(get_bridge_state_for::<TestRuntime, ()>(&dest).is_none());

			// make congested
			update_bridge_status(bridge_id, true);
			assert_eq!(
				get_bridge_state_for::<TestRuntime, ()>(&dest),
				Some(BridgeState {
					delivery_fee_factor: MINIMAL_DELIVERY_FEE_FACTOR,
					is_congested: true,
				})
			);

			// make uncongested
			update_bridge_status(bridge_id, false);
			assert_eq!(
				get_bridge_state_for::<TestRuntime, ()>(&dest),
				None
			);
		});
	}

	#[test]
	fn do_update_bridge_status_works() {
		run_test(|| {
			let dest = Location::new(2, [GlobalConsensus(BridgedNetworkId::get())]);
			let bridge_id =
				bp_xcm_bridge_hub::BridgeId::new(&UniversalLocation::get(), dest.interior());
			assert!(get_bridge_state_for::<TestRuntime, ()>(&dest).is_none());

			// update as is_congested=false when `None`
			Pallet::<TestRuntime, ()>::do_update_bridge_status(bridge_id, false);
			assert!(get_bridge_state_for::<TestRuntime, ()>(&dest).is_none());

			// update as is_congested=true
			Pallet::<TestRuntime, ()>::do_update_bridge_status(bridge_id, true);
			assert_eq!(
				get_bridge_state_for::<TestRuntime, ()>(&dest),
				Some(BridgeState {
					delivery_fee_factor: MINIMAL_DELIVERY_FEE_FACTOR,
					is_congested: true,
				})
			);

			// increase fee factor when congested
			Pallet::<TestRuntime, ()>::on_message_sent_to(5, dest.clone());
			assert!(
				get_bridge_state_for::<TestRuntime, ()>(&dest).unwrap().delivery_fee_factor > MINIMAL_DELIVERY_FEE_FACTOR
			);
			// update as is_congested=true - should not reset fee factor
			Pallet::<TestRuntime, ()>::do_update_bridge_status(bridge_id, true);
			assert!(
				get_bridge_state_for::<TestRuntime, ()>(&dest).unwrap().delivery_fee_factor > MINIMAL_DELIVERY_FEE_FACTOR
			);

			// update as is_congested=false when `Some(..)`
			Pallet::<TestRuntime, ()>::do_update_bridge_status(bridge_id, false);
			assert_eq!(
				get_bridge_state_for::<TestRuntime, ()>(&dest),
				None,
			);
		})
	}
}
