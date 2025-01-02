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

use codec::{Decode, DecodeAll, Encode};
use cumulus_primitives_core::{ParachainBlockData, PersistedValidationData};
use cumulus_test_client::{
	generate_extrinsic,
	runtime::{
		self as test_runtime, Block, Hash, Header, TestPalletCall, UncheckedExtrinsic, WASM_BINARY,
	},
	seal_block, transfer, BlockData, BlockOrigin, BuildParachainBlockData, Client,
	ClientBlockImportExt, DefaultTestClientBuilderExt, HeadData, InitBlockBuilder,
	Sr25519Keyring::{Alice, Bob, Charlie},
	TestClientBuilder, TestClientBuilderExt, ValidationParams,
};
use cumulus_test_relay_sproof_builder::RelayStateSproofBuilder;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use std::{env, process::Command};

use crate::validate_block::MemoryOptimizedValidationParams;

fn call_validate_block_encoded_header(
	validation_code: &[u8],
	parent_head: Header,
	block_data: ParachainBlockData<Block>,
	relay_parent_storage_root: Hash,
) -> cumulus_test_client::ExecutorResult<Vec<u8>> {
	cumulus_test_client::validate_block(
		ValidationParams {
			block_data: BlockData(block_data.encode()),
			parent_head: HeadData(parent_head.encode()),
			relay_parent_number: 1,
			relay_parent_storage_root,
		},
		validation_code,
	)
	.map(|v| v.head_data.0)
}

fn call_validate_block(
	parent_head: Header,
	block_data: ParachainBlockData<Block>,
	relay_parent_storage_root: Hash,
) -> cumulus_test_client::ExecutorResult<Header> {
	call_validate_block_encoded_header(
		WASM_BINARY.expect("You need to build the WASM binaries to run the tests!"),
		parent_head,
		block_data,
		relay_parent_storage_root,
	)
	.map(|v| Header::decode(&mut &v[..]).expect("Decodes `Header`."))
}

/// Call `validate_block` in the runtime with `elastic-scaling` activated.
fn call_validate_block_elastic_scaling(
	parent_head: Header,
	block_data: ParachainBlockData<Block>,
	relay_parent_storage_root: Hash,
) -> cumulus_test_client::ExecutorResult<Header> {
	call_validate_block_encoded_header(
		test_runtime::elastic_scaling::WASM_BINARY
			.expect("You need to build the WASM binaries to run the tests!"),
		parent_head,
		block_data,
		relay_parent_storage_root,
	)
	.map(|v| Header::decode(&mut &v[..]).expect("Decodes `Header`."))
}

fn create_test_client() -> (Client, Header) {
	let client = TestClientBuilder::new().enable_import_proof_recording().build();

	let genesis_header = client
		.header(client.chain_info().genesis_hash)
		.ok()
		.flatten()
		.expect("Genesis header exists; qed");

	(client, genesis_header)
}

/// Create test client using the runtime with `elastic-scaling` feature enabled.
fn create_elastic_scaling_test_client() -> (Client, Header) {
	let mut builder = TestClientBuilder::new();
	builder.genesis_init_mut().wasm = Some(
		test_runtime::elastic_scaling::WASM_BINARY
			.expect("You need to build the WASM binaries to run the tests!")
			.to_vec(),
	);
	let client = builder.enable_import_proof_recording().build();

	let genesis_header = client
		.header(client.chain_info().genesis_hash)
		.ok()
		.flatten()
		.expect("Genesis header exists; qed");

	(client, genesis_header)
}

struct TestBlockData {
	block: ParachainBlockData<Block>,
	validation_data: PersistedValidationData,
}

fn build_block_with_witness(
	client: &Client,
	extra_extrinsics: Vec<UncheckedExtrinsic>,
	parent_head: Header,
	mut sproof_builder: RelayStateSproofBuilder,
) -> TestBlockData {
	sproof_builder.para_id = test_runtime::PARACHAIN_ID.into();
	sproof_builder.included_para_head = Some(HeadData(parent_head.encode()));

	let validation_data = PersistedValidationData {
		relay_parent_number: 1,
		parent_head: parent_head.encode().into(),
		..Default::default()
	};

	let cumulus_test_client::BlockBuilderAndSupportData {
		mut block_builder,
		persisted_validation_data,
	} = client.init_block_builder(Some(validation_data), sproof_builder);

	extra_extrinsics.into_iter().for_each(|e| block_builder.push(e).unwrap());

	let block = block_builder.build_parachain_block(*parent_head.state_root());

	TestBlockData { block, validation_data: persisted_validation_data }
}

fn build_multiple_blocks_with_witness(
	client: &Client,
	mut parent_head: Header,
	mut sproof_builder: RelayStateSproofBuilder,
	num_blocks: usize,
) -> TestBlockData {
	sproof_builder.para_id = test_runtime::PARACHAIN_ID.into();
	sproof_builder.included_para_head = Some(HeadData(parent_head.encode()));
	sproof_builder.current_slot = (std::time::SystemTime::now()
		.duration_since(std::time::SystemTime::UNIX_EPOCH)
		.expect("Time is always after UNIX_EPOCH; qed")
		.as_millis() as u64 /
		6000)
		.into();

	let validation_data = PersistedValidationData {
		relay_parent_number: 1,
		parent_head: parent_head.encode().into(),
		..Default::default()
	};

	let mut persisted_validation_data = None;
	let mut blocks = Vec::new();

	for _ in 0..num_blocks {
		let cumulus_test_client::BlockBuilderAndSupportData {
			block_builder,
			persisted_validation_data: p_v_data,
		} = client.init_block_builder(Some(validation_data.clone()), sproof_builder.clone());

		persisted_validation_data = Some(p_v_data);

		blocks.extend(
			block_builder
				.build_parachain_block(*parent_head.state_root())
				.into_inner()
				.into_iter()
				.inspect(|d| {
					futures::executor::block_on(
						client.import_as_best(BlockOrigin::Own, d.0.clone()),
					)
					.unwrap();

					parent_head = d.0.header.clone();
				}),
		);
	}

	TestBlockData {
		block: ParachainBlockData::new(blocks),
		validation_data: persisted_validation_data.unwrap(),
	}
}

#[test]
fn validate_block_works() {
	sp_tracing::try_init_simple();

	let (client, parent_head) = create_test_client();
	let TestBlockData { block, validation_data } =
		build_block_with_witness(&client, Vec::new(), parent_head.clone(), Default::default());

	let block = seal_block(block, &client);
	let header = block.blocks().nth(0).unwrap().header().clone();
	let res_header =
		call_validate_block(parent_head, block, validation_data.relay_parent_storage_root)
			.expect("Calls `validate_block`");
	assert_eq!(header, res_header);
}

#[test]
fn validate_multiple_blocks_work() {
	sp_tracing::try_init_simple();

	let (client, parent_head) = create_elastic_scaling_test_client();
	let TestBlockData { block, validation_data } =
		build_multiple_blocks_with_witness(&client, parent_head.clone(), Default::default(), 4);

	let block = seal_block(block, &client);
	let header = block.blocks().last().unwrap().header().clone();
	let res_header = call_validate_block_elastic_scaling(
		parent_head,
		block,
		validation_data.relay_parent_storage_root,
	)
	.expect("Calls `validate_block`");
	assert_eq!(header, res_header);
}

#[test]
fn validate_block_with_extra_extrinsics() {
	sp_tracing::try_init_simple();

	let (client, parent_head) = create_test_client();
	let extra_extrinsics = vec![
		transfer(&client, Alice, Bob, 69),
		transfer(&client, Bob, Charlie, 100),
		transfer(&client, Charlie, Alice, 500),
	];

	let TestBlockData { block, validation_data } = build_block_with_witness(
		&client,
		extra_extrinsics,
		parent_head.clone(),
		Default::default(),
	);
	let block = seal_block(block, &client);
	let header = block.blocks().nth(0).unwrap().header().clone();

	let res_header =
		call_validate_block(parent_head, block, validation_data.relay_parent_storage_root)
			.expect("Calls `validate_block`");
	assert_eq!(header, res_header);
}

#[test]
fn validate_block_returns_custom_head_data() {
	sp_tracing::try_init_simple();

	let expected_header = vec![1, 3, 3, 7, 4, 5, 6];

	let (client, parent_head) = create_test_client();
	let extra_extrinsics = vec![
		transfer(&client, Alice, Bob, 69),
		generate_extrinsic(
			&client,
			Charlie,
			TestPalletCall::set_custom_validation_head_data {
				custom_header: expected_header.clone(),
			},
		),
		transfer(&client, Bob, Charlie, 100),
	];

	let TestBlockData { block, validation_data } = build_block_with_witness(
		&client,
		extra_extrinsics,
		parent_head.clone(),
		Default::default(),
	);
	let header = block.blocks().nth(0).unwrap().header().clone();
	assert_ne!(expected_header, header.encode());

	let block = seal_block(block, &client);
	let res_header = call_validate_block_encoded_header(
		WASM_BINARY.expect("You need to build the WASM binaries to run the tests!"),
		parent_head,
		block,
		validation_data.relay_parent_storage_root,
	)
	.expect("Calls `validate_block`");
	assert_eq!(expected_header, res_header);
}

#[test]
fn validate_block_invalid_parent_hash() {
	sp_tracing::try_init_simple();

	if env::var("RUN_TEST").is_ok() {
		let (client, parent_head) = create_test_client();
		let TestBlockData { mut block, validation_data, .. } =
			build_block_with_witness(&client, Vec::new(), parent_head.clone(), Default::default());
		block
			.blocks_mut()
			.nth(0)
			.unwrap()
			.header
			.set_parent_hash(Hash::from_low_u64_be(1));

		call_validate_block(parent_head, block, validation_data.relay_parent_storage_root)
			.unwrap_err();
	} else {
		let output = Command::new(env::current_exe().unwrap())
			.args(["validate_block_invalid_parent_hash", "--", "--nocapture"])
			.env("RUN_TEST", "1")
			.output()
			.expect("Runs the test");
		assert!(output.status.success());

		assert!(dbg!(String::from_utf8(output.stderr).unwrap())
			.contains("Parachain head needs to be the parent of the first block"));
	}
}

#[test]
fn validate_block_fails_on_invalid_validation_data() {
	sp_tracing::try_init_simple();

	if env::var("RUN_TEST").is_ok() {
		let (client, parent_head) = create_test_client();
		let TestBlockData { block, .. } =
			build_block_with_witness(&client, Vec::new(), parent_head.clone(), Default::default());

		call_validate_block(parent_head, block, Hash::random()).unwrap_err();
	} else {
		let output = Command::new(env::current_exe().unwrap())
			.args(["validate_block_fails_on_invalid_validation_data", "--", "--nocapture"])
			.env("RUN_TEST", "1")
			.output()
			.expect("Runs the test");
		assert!(output.status.success());

		assert!(dbg!(String::from_utf8(output.stderr).unwrap())
			.contains("Relay parent storage root doesn't match"));
	}
}

#[test]
fn check_inherents_are_unsigned_and_before_all_other_extrinsics() {
	sp_tracing::try_init_simple();

	if env::var("RUN_TEST").is_ok() {
		let (client, parent_head) = create_test_client();

		let TestBlockData { mut block, validation_data, .. } =
			build_block_with_witness(&client, Vec::new(), parent_head.clone(), Default::default());

		block
			.blocks_mut()
			.nth(0)
			.unwrap()
			.extrinsics
			.insert(0, transfer(&client, Alice, Bob, 69));

		call_validate_block(parent_head, block, validation_data.relay_parent_storage_root)
			.unwrap_err();
	} else {
		let output = Command::new(env::current_exe().unwrap())
			.args([
				"check_inherents_are_unsigned_and_before_all_other_extrinsics",
				"--",
				"--nocapture",
			])
			.env("RUN_TEST", "1")
			.output()
			.expect("Runs the test");
		assert!(output.status.success());

		assert!(String::from_utf8(output.stderr)
			.unwrap()
			.contains("Could not find `set_validation_data` inherent"));
	}
}

/// Test that ensures that `ValidationParams` and `MemoryOptimizedValidationParams`
/// are encoding/decoding.
#[test]
fn validation_params_and_memory_optimized_validation_params_encode_and_decode() {
	const BLOCK_DATA: &[u8] = &[1, 2, 3, 4, 5];
	const PARENT_HEAD: &[u8] = &[1, 3, 4, 5, 6, 7, 9];

	let validation_params = ValidationParams {
		block_data: BlockData(BLOCK_DATA.encode()),
		parent_head: HeadData(PARENT_HEAD.encode()),
		relay_parent_number: 1,
		relay_parent_storage_root: Hash::random(),
	};

	let encoded = validation_params.encode();

	let decoded = MemoryOptimizedValidationParams::decode_all(&mut &encoded[..]).unwrap();
	assert_eq!(decoded.relay_parent_number, validation_params.relay_parent_number);
	assert_eq!(decoded.relay_parent_storage_root, validation_params.relay_parent_storage_root);
	assert_eq!(decoded.block_data, validation_params.block_data.0);
	assert_eq!(decoded.parent_head, validation_params.parent_head.0);

	let encoded = decoded.encode();

	let decoded = ValidationParams::decode_all(&mut &encoded[..]).unwrap();
	assert_eq!(decoded, validation_params);
}

/// Test for ensuring that we are differentiating in the `validation::trie_cache` between different
/// child tries.
///
/// This is achieved by first building a block using `read_and_write_child_tries` that should set
/// the values in the child tries. In the second step we are building a second block with the same
/// extrinsic that reads the values from the child tries and it asserts that we read the correct
/// data from the state.
#[test]
fn validate_block_works_with_child_tries() {
	sp_tracing::try_init_simple();

	let (client, parent_head) = create_test_client();
	let TestBlockData { block, .. } = build_block_with_witness(
		&client,
		vec![generate_extrinsic(&client, Charlie, TestPalletCall::read_and_write_child_tries {})],
		parent_head.clone(),
		Default::default(),
	);

	let block = block.blocks().nth(0).unwrap().clone();

	futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

	let parent_head = block.header().clone();

	let TestBlockData { block, validation_data } = build_block_with_witness(
		&client,
		vec![generate_extrinsic(&client, Alice, TestPalletCall::read_and_write_child_tries {})],
		parent_head.clone(),
		Default::default(),
	);

	let block = seal_block(block, &client);
	let header = block.blocks().nth(0).unwrap().header().clone();
	let res_header =
		call_validate_block(parent_head, block, validation_data.relay_parent_storage_root)
			.expect("Calls `validate_block`");
	assert_eq!(header, res_header);
}
