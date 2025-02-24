// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Test that checks approval voting coalescing does not lag finality.

use anyhow::anyhow;

use crate::helpers::{
	assert_finality_lag_less_than, assert_finalized_block_height, assert_para_throughput,
};
use polkadot_primitives::Id as ParaId;
use serde_json::json;
use subxt::{OnlineClient, PolkadotConfig};
use zombienet_sdk::NetworkConfigBuilder;

#[tokio::test(flavor = "multi_thread")]
async fn approval_voting_coalescing_test() -> Result<(), anyhow::Error> {
	let _ = env_logger::try_init_from_env(
		env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
	);

	let images = zombienet_sdk::environment::get_images_from_env();
	let no_show_slots = 4;
	let config = NetworkConfigBuilder::new()
		.with_relaychain(|r| {
			let r = r
				.with_chain("rococo-local")
				.with_default_command("polkadot")
				.with_default_image(images.polkadot.as_str())
				.with_default_args(vec![("-lparachain=debug,runtime=debug").into()])
				.with_genesis_overrides(json!({
					"configuration": {
						"config": {
							"needed_approvals": 4,
							"relay_vrf_modulo_samples": 6,
							"no_show_slots": no_show_slots,
							"approval_voting_params": {
								"max_approval_coalesce_count": 5
							}
						}
					}
				}))
				.with_node(|node| node.with_name("validator-0"));

			(1..12)
				.fold(r, |acc, i| acc.with_node(|node| node.with_name(&format!("validator-{i}"))))
		})
		.with_parachain(|p| {
			p.with_id(2000)
				.with_default_command("undying-collator")
				.with_default_image(
					std::env::var("COL_IMAGE")
						.unwrap_or("docker.io/paritypr/colander:latest".to_string())
						.as_str(),
				)
				.cumulus_based(false)
				.with_default_args(vec![("-lparachain=debug").into()])
				.with_collator(|n| n.with_name("collator-undying-2000"))
		})
		.with_parachain(|p| {
			p.with_id(2001)
				.with_default_command("undying-collator")
				.with_default_image(
					std::env::var("COL_IMAGE")
						.unwrap_or("docker.io/paritypr/colander:latest".to_string())
						.as_str(),
				)
				.cumulus_based(false)
				.with_default_args(vec![("-lparachain=debug").into()])
				.with_collator(|n| n.with_name("collator-undying-2001"))
		})
		.with_parachain(|p| {
			p.with_id(2002)
				.with_default_command("undying-collator")
				.with_default_image(
					std::env::var("COL_IMAGE")
						.unwrap_or("docker.io/paritypr/colander:latest".to_string())
						.as_str(),
				)
				.cumulus_based(false)
				.with_default_args(vec![("-lparachain=debug").into()])
				.with_collator(|n| n.with_name("collator-undying-2002"))
		})
		.with_parachain(|p| {
			p.with_id(2003)
				.with_default_command("undying-collator")
				.with_default_image(
					std::env::var("COL_IMAGE")
						.unwrap_or("docker.io/paritypr/colander:latest".to_string())
						.as_str(),
				)
				.cumulus_based(false)
				.with_default_args(vec![("-lparachain=debug").into()])
				.with_collator(|n| n.with_name("collator-undying-2003"))
		})
		.with_parachain(|p| {
			p.with_id(2004)
				.with_default_command("undying-collator")
				.with_default_image(
					std::env::var("COL_IMAGE")
						.unwrap_or("docker.io/paritypr/colander:latest".to_string())
						.as_str(),
				)
				.cumulus_based(false)
				.with_default_args(vec![("-lparachain=debug").into()])
				.with_collator(|n| n.with_name("collator-undying-2004"))
		})
		.with_parachain(|p| {
			p.with_id(2005)
				.with_default_command("undying-collator")
				.with_default_image(
					std::env::var("COL_IMAGE")
						.unwrap_or("docker.io/paritypr/colander:latest".to_string())
						.as_str(),
				)
				.cumulus_based(false)
				.with_default_args(vec![("-lparachain=debug").into()])
				.with_collator(|n| n.with_name("collator-undying-2005"))
		})
		.with_parachain(|p| {
			p.with_id(2006)
				.with_default_command("undying-collator")
				.with_default_image(
					std::env::var("COL_IMAGE")
						.unwrap_or("docker.io/paritypr/colander:latest".to_string())
						.as_str(),
				)
				.cumulus_based(false)
				.with_default_args(vec![("-lparachain=debug").into()])
				.with_collator(|n| n.with_name("collator-undying-2006"))
		})
		.with_parachain(|p| {
			p.with_id(2007)
				.with_default_command("undying-collator")
				.with_default_image(
					std::env::var("COL_IMAGE")
						.unwrap_or("docker.io/paritypr/colander:latest".to_string())
						.as_str(),
				)
				.cumulus_based(false)
				.with_default_args(vec![("-lparachain=debug").into()])
				.with_collator(|n| n.with_name("collator-undying-2007"))
		})
		.build()
		.map_err(|e| {
			let errs = e.into_iter().map(|e| e.to_string()).collect::<Vec<_>>().join(" ");
			anyhow!("config errs: {errs}")
		})?;

	let spawn_fn = zombienet_sdk::environment::get_spawn_fn();

	log::info!("Spawning network");
	let network = spawn_fn(config).await?;

	log::info!("Waiting for network to initialize");
	let relay_node = network.get_node("validator-0")?;
	let para_node_2001 = network.get_node("collator-undying-2000")?;

	let relay_client: OnlineClient<PolkadotConfig> = relay_node.wait_client().await?;

	log::info!("Waiting for parachains to advance to block 15");
	assert_para_throughput(
		&relay_client,
		15,
		[
			(ParaId::from(2000), 11..16),
			(ParaId::from(2001), 11..16),
			(ParaId::from(2002), 11..16),
			(ParaId::from(2003), 11..16),
			(ParaId::from(2004), 11..16),
			(ParaId::from(2005), 11..16),
			(ParaId::from(2006), 11..16),
			(ParaId::from(2007), 11..16),
		]
		.into_iter()
		.collect(),
	)
	.await?;

	log::info!("Checking finality does not lag and no-shows are within range");
	for node in network.nodes() {
		assert_finality_lag_less_than(&node.wait_client().await?, no_show_slots).await?;
		assert!(
			node.reports("polkadot_parachain_approvals_no_shows_total").await.unwrap() < 3.0,
			"No-shows should be less than 3"
		);
	}

	log::info!("Test finished successfully");

	Ok(())
}
