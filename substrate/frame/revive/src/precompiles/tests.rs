// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;
use crate::tests::Test;
use sp_core::hex2array;

#[test]
fn matching_works() {
	struct Matcher1;
	struct Matcher2;

	impl PrimitivePrecompile for Matcher1 {
		type T = Test;
		const MATCHER: BuiltinAddressMatcher = BuiltinAddressMatcher::Fixed(0x42);
		const HAS_CONTRACT_INFO: bool = true;

		fn call(
			address: &[u8; 20],
			_input: &[u8],
			_env: Option<&impl Ext<T = Self::T>>,
		) -> Result<Vec<u8>, Vec<u8>> {
			Ok(address.to_vec())
		}
	}

	impl PrimitivePrecompile for Matcher2 {
		type T = Test;
		const MATCHER: BuiltinAddressMatcher = BuiltinAddressMatcher::Prefix(0x88);
		const HAS_CONTRACT_INFO: bool = false;

		fn call(
			address: &[u8; 20],
			_input: &[u8],
			_env: Option<&impl Ext<T = Self::T>>,
		) -> Result<Vec<u8>, Vec<u8>> {
			Ok(address.to_vec())
		}
	}

	type Col = (Matcher1, Matcher2);

	assert_eq!(Col::kind(&hex2array!("1000000000000000000000000000000000000043")), None,);
	assert_eq!(
		Col::kind(&hex2array!("0000000000000000000000000000000000000042")),
		Some(Kind::WithContractInfo)
	);
	assert_eq!(Col::kind(&hex2array!("1000000000000000000000000000000000000042")), None,);
	assert_eq!(
		Col::kind(&hex2array!("0000000000000000000000000000000000000088")),
		Some(Kind::NoContractInfo)
	);
	assert_eq!(
		Col::kind(&hex2array!("2200000000000000000000000000000000000088")),
		Some(Kind::NoContractInfo)
	);
	assert_eq!(
		Col::kind(&hex2array!("0010000000000000000000000000000000000088")),
		Some(Kind::NoContractInfo)
	);
	assert_eq!(Col::kind(&hex2array!("0000000010000000000000000000000000000088")), None);
}

#[test]
fn builtin_matching_works() {
	assert_eq!(
		<Builtin<Test>>::kind(&hex2array!("0000000000000000000000000000000000000001")),
		Some(Kind::NoContractInfo)
	);
	assert_eq!(
		<Builtin<Test>>::kind(&hex2array!("0000000000000000000000000000000000001000")),
		Some(Kind::NoContractInfo)
	);
	assert_eq!(
		<Builtin<Test>>::kind(&hex2array!("7000000000000000000000000000000000000001")),
		None,
	);
	assert_eq!(
		<Builtin<Test>>::kind(&hex2array!("7000000000000000000000000000000000001000")),
		None,
	);
}
