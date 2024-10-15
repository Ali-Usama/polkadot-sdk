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

//! This fixture calls itself as many times as passed as argument.

#![no_std]
#![no_main]

use common::input;
use uapi::{HostFn, HostFnImpl as api};

#[no_mangle]
#[polkavm_derive::polkavm_export]
pub extern "C" fn deploy() {}

#[no_mangle]
#[polkavm_derive::polkavm_export]
pub extern "C" fn call() {
	input!(calls_left: u32, callee_addr: &[u8; 20],);

	let next_input = (calls_left - 1).to_le_bytes();

	// Call the callee
	api::call(
		uapi::CallFlags::empty(),
		callee_addr,
		0u64,       // How much ref_time to devote for the execution. 0 = all.
		0u64,       // How much proof_size to devote for the execution. 0 = all.
		None,       // No deposit limit.
		&[0u8; 32], // Value transferred to the contract.
		&next_input,
		None,
	)
	.unwrap();

	if calls_left == 0 {
		return
	}

	// own address
	let mut addr = [0u8; 20];
	api::address(&mut addr);
	let mut input = [0u8; 24];

	input[..4].copy_from_slice(&next_input);
	input[4..24].copy_from_slice(&callee_addr[..20]);

	// recurse
	api::call(
		uapi::CallFlags::ALLOW_REENTRY,
		&addr,
		0u64,       // How much ref_time to devote for the execution. 0 = all.
		0u64,       // How much deposit_limit to devote for the execution. 0 = all.
		None,       // No deposit limit.
		&[0u8; 32], // Value transferred to the contract.
		&input,
		None,
	)
	.unwrap();
}
