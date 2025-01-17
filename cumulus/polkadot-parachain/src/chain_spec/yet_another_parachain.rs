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

//! ChainSpecs dedicated to parachain setups for testing and example purposes

use parachains_common::AccountId;
use polkadot_omni_node_lib::chain_spec::{Extensions, GenericChainSpec};
use sc_chain_spec::ChainType;
use sp_core::{hex2array, sr25519::Pair as SrPair, Pair};
use sp_keyring::Sr25519Keyring as Keyring;
use yet_another_parachain_runtime::AuraId;

const NUM_ACCOUNT_PAIRS: usize = 16000;

fn derive_accounts(n: usize, seed: String) -> Vec<SrPair> {
	let t = std::cmp::min(
		n,
		std::thread::available_parallelism().unwrap_or(1usize.try_into().unwrap()).get(),
	);

	let mut tn = (0..t).cycle();
	let mut tranges: Vec<_> = (0..t).map(|_| Vec::new()).collect();
	(0..n).for_each(|i| tranges[tn.next().unwrap()].push(i));
	let mut threads = Vec::new();

	tranges.into_iter().for_each(|chunk| {
		let seed = seed.clone();
		threads.push(std::thread::spawn(move || {
			chunk
				.into_iter()
				.map(move |i| {
					let derivation = format!("{seed}/{i}");
					<SrPair as Pair>::from_string(&derivation, None).unwrap()
				})
				.collect::<Vec<_>>()
		}));
	});

	threads
		.into_iter()
		.map(|h| h.join().unwrap())
		.flatten()
		// .map(|p| (p, funds))
		.collect()
}

pub fn yet_another_parachain_config(
	relay: impl Into<String>,
	chain_type: ChainType,
	para_id: u32,
) -> GenericChainSpec {
	// 	> subkey inspect --network kusama --public \
	// 6205a2a2aecb71c13d8ad3197e12c10bcdcaa0c9f176997bc236c6b39143aa15
	//
	// Network ID/Version: kusama
	//   Public key (hex):   0x6205a2a2aecb71c13d8ad3197e12c10bcdcaa0c9f176997bc236c6b39143aa15
	//   Account ID:         0x6205a2a2aecb71c13d8ad3197e12c10bcdcaa0c9f176997bc236c6b39143aa15
	//   Public key (SS58):  EnqtFmsXcGdSnWk5JWUMXyPVamjiFQurXxcNgJEg1C3sw6W
	//   SS58 Address:       EnqtFmsXcGdSnWk5JWUMXyPVamjiFQurXxcNgJEg1C3sw6W
	let yap_sudo: AccountId =
		hex2array!("6205a2a2aecb71c13d8ad3197e12c10bcdcaa0c9f176997bc236c6b39143aa15").into();
	let mut endowed_accounts = vec![
		yap_sudo.clone(),
		Keyring::Alice.to_account_id(),
		Keyring::Bob.to_account_id(),
		Keyring::AliceStash.to_account_id(),
		Keyring::BobStash.to_account_id(),
	];

	endowed_accounts.extend(
		derive_accounts(NUM_ACCOUNT_PAIRS, "//Sender".into())
			.into_iter()
			.map(|k| k.public().into()),
	);
	endowed_accounts.extend(
		derive_accounts(NUM_ACCOUNT_PAIRS, "//Receiver".into())
			.into_iter()
			.map(|k| k.public().into()),
	);

	GenericChainSpec::builder(
		yet_another_parachain_runtime::WASM_BINARY
			.expect("WASM binary was not built, please build it!"),
		Extensions { relay_chain: relay.into(), para_id },
	)
	.with_name("Yet Another Parachain")
	.with_id("yet_another_parachain")
	.with_chain_type(chain_type)
	.with_genesis_config_patch(serde_json::json!({
		"balances": {
			"balances": endowed_accounts.iter().cloned().map(|k| (k, 1u64 << 60)).collect::<Vec<_>>(),
		},
		"sudo": { "key": Some(yap_sudo) },
		"parachainInfo": {
			"parachainId": para_id,
		},
		"aura": { "authorities": vec![Into::<AuraId>::into(Keyring::Alice.public()), Keyring::Bob.public().into()] },
	}))
	.build()
}
