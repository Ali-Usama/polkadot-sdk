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

//! Bridge definitions that can be used by multiple BridgeHub flavors.
//! All configurations here should be dedicated to a single chain; in other words, we don't need two
//! chains for a single pallet configuration.
//!
//! For example, the messaging pallet needs to know the sending and receiving chains, but the
//! GRANDPA tracking pallet only needs to be aware of one chain.

use super::{
	weights, AccountId, Balance, Balances, BlockNumber, Runtime, RuntimeEvent, RuntimeOrigin,
};
use bp_parachains::SingleParaStoredHeaderDataBuilder;
use bp_runtime::{RelayerVersion, UnderlyingChainProvider};
use bridge_runtime_common::messages::ThisChainWithMessages;
use frame_support::{parameter_types, traits::ConstU32};
use hex_literal::hex;
use sp_core::H256;
use sp_runtime::RuntimeDebug;

parameter_types! {
	pub const RelayChainHeadersToKeep: u32 = 1024;
	pub const ParachainHeadsToKeep: u32 = 64;

	pub const WestendBridgeParachainPalletName: &'static str = bp_westend::PARAS_PALLET_NAME;
	pub const MaxWestendParaHeadDataSize: u32 = bp_westend::MAX_NESTED_PARACHAIN_HEAD_DATA_SIZE;

	pub storage RequiredStakeForStakeAndSlash: Balance = 1_000_000;
	pub const RelayerStakeLease: u32 = 8;
	pub const RelayerStakeReserveId: [u8; 8] = *b"brdgrlrs";

	pub const WithRococoBulletinCompatibleGrandpaRelayer: RelayerVersion = RelayerVersion {
		manual: 0,
		auto: H256(hex!("63c6b0bdb689ffb0e787890cf9c3171e83fdeb7e7bb1186a8ca927507317a9a6")),
	};
	pub const WithWestendCompatibleGrandpaRelayer: RelayerVersion = RelayerVersion {
		manual: 0,
		auto: H256(hex!("ed94acc451921d37f6497dc1864f4ea9cca3db53bfae3eb6da7f735ee775430a")),
	};
	pub const WithWestendCompatibleParachainsRelayer: RelayerVersion = RelayerVersion {
		manual: 0,
		auto: H256(hex!("cce194f365e85a948f84c123ab1a2b082850f665917bde2b2ef75da7937c6b5e")),
	};

	pub storage DeliveryRewardInBalance: u64 = 1_000_000;
}

/// Add GRANDPA bridge pallet to track Westend relay chain.
pub type BridgeGrandpaWestendInstance = pallet_bridge_grandpa::Instance3;
impl pallet_bridge_grandpa::Config<BridgeGrandpaWestendInstance> for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type CompatibleWithRelayer = WithWestendCompatibleGrandpaRelayer;
	type BridgedChain = bp_westend::Westend;
	type MaxFreeMandatoryHeadersPerBlock = ConstU32<4>;
	type HeadersToKeep = RelayChainHeadersToKeep;
	type WeightInfo = weights::pallet_bridge_grandpa::WeightInfo<Runtime>;
}

/// Add parachain bridge pallet to track Westend BridgeHub parachain
pub type BridgeParachainWestendInstance = pallet_bridge_parachains::Instance3;
impl pallet_bridge_parachains::Config<BridgeParachainWestendInstance> for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type CompatibleWithRelayer = WithWestendCompatibleParachainsRelayer;
	type WeightInfo = weights::pallet_bridge_parachains::WeightInfo<Runtime>;
	type BridgesGrandpaPalletInstance = BridgeGrandpaWestendInstance;
	type ParasPalletName = WestendBridgeParachainPalletName;
	type ParaStoredHeaderDataBuilder =
		SingleParaStoredHeaderDataBuilder<bp_bridge_hub_westend::BridgeHubWestend>;
	type HeadsToKeep = ParachainHeadsToKeep;
	type MaxParaHeadDataSize = MaxWestendParaHeadDataSize;
}

/// Allows collect and claim rewards for relayers
impl pallet_bridge_relayers::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type Reward = Balance;
	type PaymentProcedure =
		bp_relayers::PayRewardFromAccount<pallet_balances::Pallet<Runtime>, AccountId>;
	type StakeAndSlash = pallet_bridge_relayers::StakeAndSlashNamed<
		AccountId,
		BlockNumber,
		Balances,
		RelayerStakeReserveId,
		RequiredStakeForStakeAndSlash,
		RelayerStakeLease,
	>;
	type WeightInfo = weights::pallet_bridge_relayers::WeightInfo<Runtime>;
}

/// Add GRANDPA bridge pallet to track Rococo Bulletin chain.
pub type BridgeGrandpaRococoBulletinInstance = pallet_bridge_grandpa::Instance4;
impl pallet_bridge_grandpa::Config<BridgeGrandpaRococoBulletinInstance> for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type CompatibleWithRelayer = WithRococoBulletinCompatibleGrandpaRelayer;
	type BridgedChain = bp_polkadot_bulletin::PolkadotBulletin;
	type MaxFreeMandatoryHeadersPerBlock = ConstU32<4>;
	type HeadersToKeep = RelayChainHeadersToKeep;
	// Technically this is incorrect - we have two pallet instances and ideally we shall
	// benchmark every instance separately. But the benchmarking engine has a flaw - it
	// messes with components. E.g. in Kusama maximal validators count is 1024 and in
	// Bulletin chain it is 100. But benchmarking engine runs Bulletin benchmarks using
	// components range, computed for Kusama => it causes an error.
	//
	// In practice, however, GRANDPA pallet works the same way for all bridged chains, so
	// weights are also the same for both bridges.
	type WeightInfo = weights::pallet_bridge_grandpa::WeightInfo<Runtime>;
}

/// BridgeHubRococo chain from message lane point of view.
#[derive(RuntimeDebug, Clone, Copy)]
pub struct BridgeHubRococo;

impl UnderlyingChainProvider for BridgeHubRococo {
	type Chain = bp_bridge_hub_rococo::BridgeHubRococo;
}

impl ThisChainWithMessages for BridgeHubRococo {
	type RuntimeOrigin = RuntimeOrigin;
}
