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

//! Autogenerated weights for `pallet_bridge_messages`
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 32.0.0
//! DATE: 2025-01-20, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `86c039759f6a`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! WASM-EXECUTION: `Compiled`, CHAIN: `Some("bridge-hub-rococo-dev")`, DB CACHE: 1024

// Executed Command:
// target/production/polkadot-parachain
// benchmark
// pallet
// --extrinsic=*
// --chain=bridge-hub-rococo-dev
// --pallet=pallet_bridge_messages
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

/// Weight functions for `pallet_bridge_messages`.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_bridge_messages::WeightInfo for WeightInfo<T> {
	/// Storage: `BridgeWestendMessages::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendMessages::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendParachains::ImportedParaHeads` (r:1 w:0)
	/// Proof: `BridgeWestendParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::InboundLanes` (r:1 w:1)
	/// Proof: `BridgeWestendMessages::InboundLanes` (`max_values`: None, `max_size`: Some(49180), added: 51655, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::LaneToBridge` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::LaneToBridge` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::Bridges` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::Bridges` (`max_values`: None, `max_size`: Some(1889), added: 4364, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::OutboundXcmpStatus` (r:1 w:0)
	/// Proof: `XcmpQueue::OutboundXcmpStatus` (`max_values`: Some(1), `max_size`: Some(1282), added: 1777, mode: `MaxEncodedLen`)
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn receive_single_message_proof() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `833`
		//  Estimated: `52645`
		// Minimum execution time: 64_919_000 picoseconds.
		Weight::from_parts(66_807_000, 0)
			.saturating_add(Weight::from_parts(0, 52645))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `BridgeWestendMessages::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendMessages::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendParachains::ImportedParaHeads` (r:1 w:0)
	/// Proof: `BridgeWestendParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::InboundLanes` (r:1 w:1)
	/// Proof: `BridgeWestendMessages::InboundLanes` (`max_values`: None, `max_size`: Some(49180), added: 51655, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::LaneToBridge` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::LaneToBridge` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::Bridges` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::Bridges` (`max_values`: None, `max_size`: Some(1889), added: 4364, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::OutboundXcmpStatus` (r:1 w:0)
	/// Proof: `XcmpQueue::OutboundXcmpStatus` (`max_values`: Some(1), `max_size`: Some(1282), added: 1777, mode: `MaxEncodedLen`)
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[1, 4076]`.
	/// The range of component `n` is `[1, 4076]`.
	fn receive_n_messages_proof(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `833`
		//  Estimated: `52645`
		// Minimum execution time: 64_855_000 picoseconds.
		Weight::from_parts(65_887_000, 0)
			.saturating_add(Weight::from_parts(0, 52645))
			// Standard Error: 14_029
			.saturating_add(Weight::from_parts(11_461_737, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `BridgeWestendMessages::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendMessages::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendParachains::ImportedParaHeads` (r:1 w:0)
	/// Proof: `BridgeWestendParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::InboundLanes` (r:1 w:1)
	/// Proof: `BridgeWestendMessages::InboundLanes` (`max_values`: None, `max_size`: Some(49180), added: 51655, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::LaneToBridge` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::LaneToBridge` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::Bridges` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::Bridges` (`max_values`: None, `max_size`: Some(1889), added: 4364, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::OutboundXcmpStatus` (r:1 w:0)
	/// Proof: `XcmpQueue::OutboundXcmpStatus` (`max_values`: Some(1), `max_size`: Some(1282), added: 1777, mode: `MaxEncodedLen`)
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	fn receive_single_message_proof_with_outbound_lane_state() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `833`
		//  Estimated: `52645`
		// Minimum execution time: 70_467_000 picoseconds.
		Weight::from_parts(72_324_000, 0)
			.saturating_add(Weight::from_parts(0, 52645))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `BridgeWestendMessages::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendMessages::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendParachains::ImportedParaHeads` (r:1 w:0)
	/// Proof: `BridgeWestendParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::InboundLanes` (r:1 w:1)
	/// Proof: `BridgeWestendMessages::InboundLanes` (`max_values`: None, `max_size`: Some(49180), added: 51655, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::LaneToBridge` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::LaneToBridge` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::Bridges` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::Bridges` (`max_values`: None, `max_size`: Some(1889), added: 4364, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::OutboundXcmpStatus` (r:1 w:0)
	/// Proof: `XcmpQueue::OutboundXcmpStatus` (`max_values`: Some(1), `max_size`: Some(1282), added: 1777, mode: `MaxEncodedLen`)
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[1, 16384]`.
	/// The range of component `n` is `[1, 16384]`.
	fn receive_single_n_bytes_message_proof(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `833`
		//  Estimated: `52645`
		// Minimum execution time: 63_251_000 picoseconds.
		Weight::from_parts(66_362_094, 0)
			.saturating_add(Weight::from_parts(0, 52645))
			// Standard Error: 18
			.saturating_add(Weight::from_parts(2_152, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	/// Storage: `BridgeWestendMessages::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendMessages::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendParachains::ImportedParaHeads` (r:1 w:0)
	/// Proof: `BridgeWestendParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::OutboundLanes` (r:1 w:1)
	/// Proof: `BridgeWestendMessages::OutboundLanes` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x6e0a18b62a1de81c5f519181cc611e18` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x6e0a18b62a1de81c5f519181cc611e18` (r:1 w:0)
	/// Storage: `BridgeRelayers::RelayerRewards` (r:1 w:1)
	/// Proof: `BridgeRelayers::RelayerRewards` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::LaneToBridge` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::LaneToBridge` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::Bridges` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::Bridges` (`max_values`: None, `max_size`: Some(1889), added: 4364, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::OutboundMessages` (r:0 w:1)
	/// Proof: `BridgeWestendMessages::OutboundMessages` (`max_values`: None, `max_size`: Some(65568), added: 68043, mode: `MaxEncodedLen`)
	fn receive_delivery_proof_for_single_message() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `776`
		//  Estimated: `5354`
		// Minimum execution time: 54_017_000 picoseconds.
		Weight::from_parts(56_500_000, 0)
			.saturating_add(Weight::from_parts(0, 5354))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(3))
	}
	/// Storage: `BridgeWestendMessages::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendMessages::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendParachains::ImportedParaHeads` (r:1 w:0)
	/// Proof: `BridgeWestendParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::OutboundLanes` (r:1 w:1)
	/// Proof: `BridgeWestendMessages::OutboundLanes` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x6e0a18b62a1de81c5f519181cc611e18` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x6e0a18b62a1de81c5f519181cc611e18` (r:1 w:0)
	/// Storage: `BridgeRelayers::RelayerRewards` (r:1 w:1)
	/// Proof: `BridgeRelayers::RelayerRewards` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::LaneToBridge` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::LaneToBridge` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::Bridges` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::Bridges` (`max_values`: None, `max_size`: Some(1889), added: 4364, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::OutboundMessages` (r:0 w:2)
	/// Proof: `BridgeWestendMessages::OutboundMessages` (`max_values`: None, `max_size`: Some(65568), added: 68043, mode: `MaxEncodedLen`)
	fn receive_delivery_proof_for_two_messages_by_single_relayer() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `776`
		//  Estimated: `5354`
		// Minimum execution time: 55_587_000 picoseconds.
		Weight::from_parts(56_972_000, 0)
			.saturating_add(Weight::from_parts(0, 5354))
			.saturating_add(T::DbWeight::get().reads(7))
			.saturating_add(T::DbWeight::get().writes(4))
	}
	/// Storage: `BridgeWestendMessages::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendMessages::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendParachains::ImportedParaHeads` (r:1 w:0)
	/// Proof: `BridgeWestendParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::OutboundLanes` (r:1 w:1)
	/// Proof: `BridgeWestendMessages::OutboundLanes` (`max_values`: None, `max_size`: Some(45), added: 2520, mode: `MaxEncodedLen`)
	/// Storage: UNKNOWN KEY `0x6e0a18b62a1de81c5f519181cc611e18` (r:1 w:0)
	/// Proof: UNKNOWN KEY `0x6e0a18b62a1de81c5f519181cc611e18` (r:1 w:0)
	/// Storage: `BridgeRelayers::RelayerRewards` (r:2 w:2)
	/// Proof: `BridgeRelayers::RelayerRewards` (`max_values`: None, `max_size`: Some(73), added: 2548, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::LaneToBridge` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::LaneToBridge` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::Bridges` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::Bridges` (`max_values`: None, `max_size`: Some(1889), added: 4364, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::OutboundMessages` (r:0 w:2)
	/// Proof: `BridgeWestendMessages::OutboundMessages` (`max_values`: None, `max_size`: Some(65568), added: 68043, mode: `MaxEncodedLen`)
	fn receive_delivery_proof_for_two_messages_by_two_relayers() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `776`
		//  Estimated: `6086`
		// Minimum execution time: 59_936_000 picoseconds.
		Weight::from_parts(62_281_000, 0)
			.saturating_add(Weight::from_parts(0, 6086))
			.saturating_add(T::DbWeight::get().reads(8))
			.saturating_add(T::DbWeight::get().writes(5))
	}
	/// Storage: `BridgeWestendMessages::PalletOperatingMode` (r:1 w:0)
	/// Proof: `BridgeWestendMessages::PalletOperatingMode` (`max_values`: Some(1), `max_size`: Some(2), added: 497, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendParachains::ImportedParaHeads` (r:1 w:0)
	/// Proof: `BridgeWestendParachains::ImportedParaHeads` (`max_values`: Some(64), `max_size`: Some(196), added: 1186, mode: `MaxEncodedLen`)
	/// Storage: `BridgeWestendMessages::InboundLanes` (r:1 w:1)
	/// Proof: `BridgeWestendMessages::InboundLanes` (`max_values`: None, `max_size`: Some(49180), added: 51655, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::LaneToBridge` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::LaneToBridge` (`max_values`: None, `max_size`: Some(36), added: 2511, mode: `MaxEncodedLen`)
	/// Storage: `XcmOverBridgeHubWestend::Bridges` (r:1 w:0)
	/// Proof: `XcmOverBridgeHubWestend::Bridges` (`max_values`: None, `max_size`: Some(1889), added: 4364, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::OutboundXcmpStatus` (r:1 w:1)
	/// Proof: `XcmpQueue::OutboundXcmpStatus` (`max_values`: Some(1), `max_size`: Some(1282), added: 1777, mode: `MaxEncodedLen`)
	/// Storage: `ParachainInfo::ParachainId` (r:1 w:0)
	/// Proof: `ParachainInfo::ParachainId` (`max_values`: Some(1), `max_size`: Some(4), added: 499, mode: `MaxEncodedLen`)
	/// Storage: `XcmpQueue::DeliveryFeeFactor` (r:1 w:0)
	/// Proof: `XcmpQueue::DeliveryFeeFactor` (`max_values`: None, `max_size`: Some(28), added: 2503, mode: `MaxEncodedLen`)
	/// Storage: `PolkadotXcm::SupportedVersion` (r:1 w:0)
	/// Proof: `PolkadotXcm::SupportedVersion` (`max_values`: None, `max_size`: None, mode: `Measured`)
	/// Storage: `ParachainSystem::RelevantMessagingState` (r:1 w:0)
	/// Proof: `ParachainSystem::RelevantMessagingState` (`max_values`: Some(1), `max_size`: None, mode: `Measured`)
	/// Storage: `XcmpQueue::OutboundXcmpMessages` (r:0 w:1)
	/// Proof: `XcmpQueue::OutboundXcmpMessages` (`max_values`: None, `max_size`: Some(105506), added: 107981, mode: `MaxEncodedLen`)
	/// The range of component `n` is `[1, 16384]`.
	/// The range of component `n` is `[1, 16384]`.
	fn receive_single_n_bytes_message_proof_with_dispatch(n: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `932`
		//  Estimated: `52645`
		// Minimum execution time: 85_185_000 picoseconds.
		Weight::from_parts(88_585_196, 0)
			.saturating_add(Weight::from_parts(0, 52645))
			// Standard Error: 23
			.saturating_add(Weight::from_parts(7_456, 0).saturating_mul(n.into()))
			.saturating_add(T::DbWeight::get().reads(10))
			.saturating_add(T::DbWeight::get().writes(3))
	}
}
