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

use cumulus_primitives_core::ParaId;
use parachains_common::Balance as PeopleBalance;
use polkadot_omni_node_lib::chain_spec::GenericChainSpec;
use sc_chain_spec::ChainSpec;
use std::str::FromStr;

/// Collects all supported People configurations.
#[derive(Debug, PartialEq)]
pub enum PeopleRuntimeType {
	Kusama,
	KusamaLocal,
	Polkadot,
	PolkadotLocal,
	Rococo,
	RococoLocal,
	RococoDevelopment,
	Westend,
	WestendLocal,
	WestendDevelopment,
}

impl FromStr for PeopleRuntimeType {
	type Err = String;

	fn from_str(value: &str) -> Result<Self, Self::Err> {
		match value {
			kusama::PEOPLE_KUSAMA => Ok(PeopleRuntimeType::Kusama),
			kusama::PEOPLE_KUSAMA_LOCAL => Ok(PeopleRuntimeType::KusamaLocal),
			polkadot::PEOPLE_POLKADOT => Ok(PeopleRuntimeType::Polkadot),
			polkadot::PEOPLE_POLKADOT_LOCAL => Ok(PeopleRuntimeType::PolkadotLocal),
			rococo::PEOPLE_ROCOCO => Ok(PeopleRuntimeType::Rococo),
			rococo::PEOPLE_ROCOCO_LOCAL => Ok(PeopleRuntimeType::RococoLocal),
			rococo::PEOPLE_ROCOCO_DEVELOPMENT => Ok(PeopleRuntimeType::RococoDevelopment),
			westend::PEOPLE_WESTEND => Ok(PeopleRuntimeType::Westend),
			westend::PEOPLE_WESTEND_LOCAL => Ok(PeopleRuntimeType::WestendLocal),
			westend::PEOPLE_WESTEND_DEVELOPMENT => Ok(PeopleRuntimeType::WestendDevelopment),
			_ => Err(format!("Value '{}' is not configured yet", value)),
		}
	}
}

impl PeopleRuntimeType {
	pub const ID_PREFIX: &'static str = "people";

	pub fn load_config(&self) -> Result<Box<dyn ChainSpec>, String> {
		match self {
			PeopleRuntimeType::Kusama => Ok(Box::new(GenericChainSpec::from_json_bytes(
				&include_bytes!("../../chain-specs/people-kusama.json")[..],
			)?)),
			PeopleRuntimeType::Polkadot => Ok(Box::new(GenericChainSpec::from_json_bytes(
				&include_bytes!("../../chain-specs/people-polkadot.json")[..],
			)?)),
			PeopleRuntimeType::Rococo => Ok(Box::new(GenericChainSpec::from_json_bytes(
				&include_bytes!("../../chain-specs/people-rococo.json")[..],
			)?)),
			PeopleRuntimeType::RococoLocal => Ok(Box::new(rococo::local_config(
				rococo::PEOPLE_ROCOCO_LOCAL,
				"Rococo People Local",
				"rococo-local",
				ParaId::new(1004),
			))),
			PeopleRuntimeType::RococoDevelopment => Ok(Box::new(rococo::local_config(
				rococo::PEOPLE_ROCOCO_DEVELOPMENT,
				"Rococo People Development",
				"rococo-development",
				ParaId::new(1004),
			))),
			PeopleRuntimeType::Westend => Ok(Box::new(GenericChainSpec::from_json_bytes(
				&include_bytes!("../../chain-specs/people-westend.json")[..],
			)?)),
			PeopleRuntimeType::WestendLocal => Ok(Box::new(westend::local_config(
				westend::PEOPLE_WESTEND_LOCAL,
				"Westend People Local",
				"westend-local",
				ParaId::new(1004),
			))),
			PeopleRuntimeType::WestendDevelopment => Ok(Box::new(westend::local_config(
				westend::PEOPLE_WESTEND_DEVELOPMENT,
				"Westend People Development",
				"westend-development",
				ParaId::new(1004),
			))),
			other => Err(std::format!(
				"No default config present for {:?}, you should provide a chain-spec as json file!",
				other
			)),
		}
	}
}

/// Check if `id` satisfies People-like format.
fn ensure_id(id: &str) -> Result<&str, String> {
	if id.starts_with(PeopleRuntimeType::ID_PREFIX) {
		Ok(id)
	} else {
		Err(format!(
			"Invalid 'id' attribute ({}), should start with prefix: {}",
			id,
			PeopleRuntimeType::ID_PREFIX
		))
	}
}

/// Sub-module for Rococo setup.
pub mod rococo {
	use super::{ParaId, PeopleBalance};
	use crate::chain_spec::SAFE_XCM_VERSION;
	use parachains_common::{AccountId, AuraId};
	use polkadot_omni_node_lib::chain_spec::{Extensions, GenericChainSpec};
	use sc_chain_spec::ChainType;
	use sp_keyring::Sr25519Keyring;

	pub(crate) const PEOPLE_ROCOCO: &str = "people-rococo";
	pub(crate) const PEOPLE_ROCOCO_LOCAL: &str = "people-rococo-local";
	pub(crate) const PEOPLE_ROCOCO_DEVELOPMENT: &str = "people-rococo-dev";
	const PEOPLE_ROCOCO_ED: PeopleBalance = people_rococo_runtime::ExistentialDeposit::get();

	pub fn local_config(
		id: &str,
		chain_name: &str,
		relay_chain: &str,
		para_id: ParaId,
	) -> GenericChainSpec {
		let mut properties = sc_chain_spec::Properties::new();
		properties.insert("ss58Format".into(), 42.into());
		properties.insert("tokenSymbol".into(), "ROC".into());
		properties.insert("tokenDecimals".into(), 12.into());

		GenericChainSpec::builder(
			people_rococo_runtime::WASM_BINARY
				.expect("WASM binary was not built, please build it!"),
			Extensions { relay_chain: relay_chain.to_string(), para_id: para_id.into() },
		)
		.with_name(chain_name)
		.with_id(super::ensure_id(id).expect("invalid id"))
		.with_chain_type(ChainType::Local)
		.with_genesis_config_patch(genesis(
			// initial collators.
			vec![
				(Sr25519Keyring::Alice.to_account_id(), Sr25519Keyring::Alice.public().into()),
				(Sr25519Keyring::Bob.to_account_id(), Sr25519Keyring::Bob.public().into()),
			],
			Sr25519Keyring::well_known().map(|k| k.to_account_id()).collect(),
			para_id,
		))
		.with_properties(properties)
		.build()
	}

	fn genesis(
		invulnerables: Vec<(AccountId, AuraId)>,
		endowed_accounts: Vec<AccountId>,
		id: ParaId,
	) -> serde_json::Value {
		serde_json::json!({
			"balances": {
				"balances": endowed_accounts
					.iter()
					.cloned()
					.map(|k| (k, PEOPLE_ROCOCO_ED * 524_288))
					.collect::<Vec<_>>(),
			},
			"parachainInfo": {
				"parachainId": id,
			},
			"collatorSelection": {
				"invulnerables": invulnerables
					.iter()
					.cloned()
					.map(|(acc, _)| acc)
					.collect::<Vec<_>>(),
				"candidacyBond": PEOPLE_ROCOCO_ED * 16,
			},
			"session": {
				"keys": invulnerables
					.into_iter()
					.map(|(acc, aura)| {
						(
							acc.clone(),                                 // account id
							acc,                                         // validator id
							people_rococo_runtime::SessionKeys { aura }, // session keys
						)
					})
					.collect::<Vec<_>>(),
			},
			"polkadotXcm": {
				"safeXcmVersion": Some(SAFE_XCM_VERSION),
			}
		})
	}
}

/// Sub-module for Westend setup.
pub mod westend {
	use super::{ParaId, PeopleBalance};
	use crate::chain_spec::SAFE_XCM_VERSION;
	use parachains_common::{AccountId, AuraId};
	use polkadot_omni_node_lib::chain_spec::{Extensions, GenericChainSpec};
	use sc_chain_spec::ChainType;
	use sp_keyring::Sr25519Keyring;

	pub(crate) const PEOPLE_WESTEND: &str = "people-westend";
	pub(crate) const PEOPLE_WESTEND_LOCAL: &str = "people-westend-local";
	pub(crate) const PEOPLE_WESTEND_DEVELOPMENT: &str = "people-westend-dev";
	const PEOPLE_WESTEND_ED: PeopleBalance = people_westend_runtime::ExistentialDeposit::get();

	pub fn local_config(
		id: &str,
		chain_name: &str,
		relay_chain: &str,
		para_id: ParaId,
	) -> GenericChainSpec {
		let mut properties = sc_chain_spec::Properties::new();
		properties.insert("ss58Format".into(), 42.into());
		properties.insert("tokenSymbol".into(), "WND".into());
		properties.insert("tokenDecimals".into(), 12.into());

		GenericChainSpec::builder(
			people_westend_runtime::WASM_BINARY
				.expect("WASM binary was not built, please build it!"),
			Extensions { relay_chain: relay_chain.to_string(), para_id: para_id.into() },
		)
		.with_name(chain_name)
		.with_id(super::ensure_id(id).expect("invalid id"))
		.with_chain_type(ChainType::Local)
		.with_genesis_config_patch(genesis(
			// initial collators.
			vec![
				(Sr25519Keyring::Alice.to_account_id(), Sr25519Keyring::Alice.public().into()),
				(Sr25519Keyring::Bob.to_account_id(), Sr25519Keyring::Bob.public().into()),
			],
			Sr25519Keyring::well_known().map(|k| k.to_account_id()).collect(),
			para_id,
		))
		.with_properties(properties)
		.build()
	}

	fn genesis(
		invulnerables: Vec<(AccountId, AuraId)>,
		endowed_accounts: Vec<AccountId>,
		id: ParaId,
	) -> serde_json::Value {
		serde_json::json!({
			"balances": {
				"balances": endowed_accounts
					.iter()
					.cloned()
					.map(|k| (k, PEOPLE_WESTEND_ED * 524_288))
					.collect::<Vec<_>>(),
			},
			"parachainInfo": {
				"parachainId": id,
			},
			"collatorSelection": {
				"invulnerables": invulnerables
					.iter()
					.cloned()
					.map(|(acc, _)| acc)
					.collect::<Vec<_>>(),
				"candidacyBond": PEOPLE_WESTEND_ED * 16,
			},
			"session": {
				"keys": invulnerables
					.into_iter()
					.map(|(acc, aura)| {
						(
							acc.clone(),                                  // account id
							acc,                                          // validator id
							people_westend_runtime::SessionKeys { aura }, // session keys
						)
					})
					.collect::<Vec<_>>(),
			},
			"polkadotXcm": {
				"safeXcmVersion": Some(SAFE_XCM_VERSION),
			}
		})
	}
}

pub mod kusama {
	pub(crate) const PEOPLE_KUSAMA: &str = "people-kusama";
	pub(crate) const PEOPLE_KUSAMA_LOCAL: &str = "people-kusama-local";
}

pub mod polkadot {
	pub(crate) const PEOPLE_POLKADOT: &str = "people-polkadot";
	pub(crate) const PEOPLE_POLKADOT_LOCAL: &str = "people-polkadot-local";
}
