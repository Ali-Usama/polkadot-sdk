// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Various utilities for testing.

pub use crate::{
	host::{EXECUTE_BINARY_NAME, PREPARE_BINARY_NAME},
	worker_interface::{spawn_with_program_path, SpawnErr},
};

use crate::{artifacts::ArtifactId, get_worker_version};
use is_executable::IsExecutable;
use polkadot_node_core_pvf_common::pvf::PvfPrepData;
use polkadot_node_primitives::NODE_VERSION;
use polkadot_primitives::ExecutorParams;
use std::{
	path::PathBuf,
	sync::{Mutex, OnceLock},
};

/// A function that emulates the stitches together behaviors of the preparation and the execution
/// worker in a single synchronous function.
pub fn validate_candidate(
	code: &[u8],
	params: &[u8],
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
	use polkadot_node_core_pvf_common::executor_interface::{prepare, prevalidate};
	use polkadot_node_core_pvf_execute_worker::{execute_pvm, execute_wasm};
	use sp_maybe_compressed_blob::{blob_type, decompress_as, MaybeCompressedBlobType};

	let blob_type = blob_type(code)?;
	assert!(blob_type.is_code());

	let code = decompress_as(blob_type, code, 10 * 1024 * 1024).expect("Decompressing code failed");

	let executor_params = ExecutorParams::default();

	let result = match blob_type {
		MaybeCompressedBlobType::Legacy | MaybeCompressedBlobType::Wasm => {
			let blob = prevalidate(&code)?;
			let compiled_artifact_blob = prepare(blob, &executor_params)?;
			unsafe { execute_wasm(&compiled_artifact_blob, &executor_params, params)? }
		},
		MaybeCompressedBlobType::Pvm => execute_pvm(&code, &executor_params, params)?,
		MaybeCompressedBlobType::Pov => unreachable!("PoV blob can never be passed as code"),
	};

	Ok(result)
}

/// Retrieves the worker paths and builds workers as needed.
///
/// NOTE: This should only be called in dev code (tests, benchmarks) as it relies on the relative
/// paths of the built workers.
pub fn build_workers_and_get_paths() -> (PathBuf, PathBuf) {
	// Only needs to be called once for the current process.
	static WORKER_PATHS: OnceLock<Mutex<(PathBuf, PathBuf)>> = OnceLock::new();

	fn build_workers() {
		let mut build_args = vec![
			"build",
			"--package=polkadot",
			"--bin=polkadot-prepare-worker",
			"--bin=polkadot-execute-worker",
		];

		if cfg!(build_profile = "release") {
			build_args.push("--release");
		}

		let mut cargo = std::process::Command::new("cargo");
		let cmd = cargo
			// wasm runtime not needed
			.env("SKIP_WASM_BUILD", "1")
			.args(build_args)
			.stdout(std::process::Stdio::piped());

		println!("INFO: calling `{cmd:?}`");
		let exit_status = cmd.status().expect("Failed to run the build program");

		if !exit_status.success() {
			eprintln!("ERROR: Failed to build workers: {}", exit_status.code().unwrap());
			std::process::exit(1);
		}
	}

	let mutex = WORKER_PATHS.get_or_init(|| {
		let mut workers_path = std::env::current_exe().unwrap();
		workers_path.pop();
		workers_path.pop();
		let mut prepare_worker_path = workers_path.clone();
		prepare_worker_path.push(PREPARE_BINARY_NAME);
		let mut execute_worker_path = workers_path.clone();
		execute_worker_path.push(EXECUTE_BINARY_NAME);

		// explain why a build happens
		if !prepare_worker_path.is_executable() {
			println!("WARN: Prepare worker does not exist or is not executable. Workers directory: {:?}", workers_path);
		}
		if !execute_worker_path.is_executable() {
			println!("WARN: Execute worker does not exist or is not executable. Workers directory: {:?}", workers_path);
		}
		if let Ok(ver) = get_worker_version(&prepare_worker_path) {
			if ver != NODE_VERSION {
				println!("WARN: Prepare worker version {ver} does not match node version {NODE_VERSION}; worker path: {prepare_worker_path:?}");
			}
		}
		if let Ok(ver) = get_worker_version(&execute_worker_path) {
			if ver != NODE_VERSION {
				println!("WARN: Execute worker version {ver} does not match node version {NODE_VERSION}; worker path: {execute_worker_path:?}");
			}
		}

		build_workers();

		Mutex::new((prepare_worker_path, execute_worker_path))
	});

	let guard = mutex.lock().unwrap();
	(guard.0.clone(), guard.1.clone())
}

/// Creates a new PVF which artifact id can be uniquely identified by the given number.
pub fn artifact_id(discriminator: u32) -> ArtifactId {
	ArtifactId::from_pvf_prep_data(&PvfPrepData::from_discriminator(discriminator))
}
