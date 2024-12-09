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

//! Exposes types that can be used to `pallet_revive` with additional functionality.
//!
//! Use `alloy` through our re-ep

mod builtin;

#[cfg(test)]
mod tests;

pub use crate::exec::Ext;
pub use alloy_core as alloy;

use crate::{precompiles::builtin::Builtin, Config};
use alloc::vec::Vec;
use alloy::sol_types::{Panic, PanicKind, Revert, SolError, SolInterface};

/// The composition of all available pre-compiles.
pub(crate) type AllPrecompiles<T> = (Builtin<T>, <T as Config>::Precompiles);

/// A type to be used by [`Precompile`] to declare at which addresses it will be called.
pub enum AddressMatcher {
	/// The pre-compile will only be called for a single address.
	Fixed(u32),
	/// The pre-compile will be called for all addresses starting with the specified prefix.
	///
	/// When using a prefix matcher `[Self::HAS_CONTRACT_INFO]` has to be set to `false`. This is
	/// enforced at compile time.
	Prefix(u32),
}

pub(crate) enum BuiltinAddressMatcher {
	Fixed(u64),
	Prefix(u64),
}

/// The only interface available for external code to extend this pallet.
pub trait Precompile {
	type T: Config;
	/// The Solidity ABI definition of this pre-compile.
	///
	/// Use the [`alloy::sol`] macro to define your interface using Solidity syntax.
	type Interface: SolInterface;
	/// Defines at which addresses this pre-compile exists.
	const MATCHER: AddressMatcher;
	/// Defines whether this pre-compile has access to stateful APIs.
	///
	/// # When set to **false**
	///
	/// - An account will be created at the pre-compiles address when it is called for the first
	///   time. The ed is minted.
	/// - Contract metadata will be created in storage on first call.
	/// - Only `call` is called.
	///
	/// # When set to **true**
	///
	/// - No account or any other state will be created for the address.
	/// - Only `call_stateless` is called.
	///
	/// # What to use
	///
	/// Should be set to true of possible. Set to false if necessary. A stateful pre-compile will
	/// incure both a storage read and write to its contract metadata when called.
	///
	/// The state enables additional functionality:
	/// - Storage deposits: Collect deposits from the origin rather than the caller. This makes it
	///   easier for contracts to interact with your pre-compile as deposits
	/// 	are payed by the transaction signer (just like gas).
	/// - Contract storage: You can use the contracts key value child trie storage instead of
	///   providing your own state.
	/// 	The contract storage automatically takes care of deposits.
	/// 	Providing your own storage and using pallet_revive to collect deposits is also possible,
	/// though.
	/// - Locking other contracts: Contracts have the ability to terminate. This can be dangerous
	///   when one relies on their existence. This is mostly relevant for delegate calls.
	/// 	We provide an API to lock a contract for a deposit.
	const HAS_CONTRACT_INFO: bool;

	fn call(
		address: &[u8; 20],
		input: &Self::Interface,
		env: Option<&impl Ext<T = Self::T>>,
	) -> Result<Vec<u8>, Revert>;
}

pub(crate) trait BuiltinPrecompile {
	type T: Config;
	type Interface: SolInterface;
	const MATCHER: BuiltinAddressMatcher;
	const HAS_CONTRACT_INFO: bool;

	fn call(
		address: &[u8; 20],
		input: &Self::Interface,
		env: Option<&impl Ext<T = Self::T>>,
	) -> Result<Vec<u8>, Revert>;
}

pub(crate) trait PrimitivePrecompile {
	type T: Config;
	const MATCHER: BuiltinAddressMatcher;
	const HAS_CONTRACT_INFO: bool;

	fn call(
		address: &[u8; 20],
		input: &[u8],
		env: Option<&impl Ext<T = Self::T>>,
	) -> Result<Vec<u8>, Vec<u8>>;
}

#[derive(PartialEq, Eq, Debug)]
pub(crate) enum Kind {
	NoContractInfo,
	WithContractInfo,
}

pub(crate) trait Precompiles<T: Config> {
	const CHECK_COLLISION: ();

	fn kind(address: &[u8; 20]) -> Option<Kind>;

	fn call(
		address: &[u8; 20],
		input: &[u8],
		env: &impl Ext<T = T>,
	) -> Option<Result<Vec<u8>, Vec<u8>>>;
}

impl<P: Precompile> BuiltinPrecompile for P {
	type T = <Self as Precompile>::T;
	type Interface = <Self as Precompile>::Interface;
	const MATCHER: BuiltinAddressMatcher = P::MATCHER.into_builtin();
	const HAS_CONTRACT_INFO: bool = P::HAS_CONTRACT_INFO;

	fn call(
		address: &[u8; 20],
		input: &Self::Interface,
		env: Option<&impl Ext<T = Self::T>>,
	) -> Result<Vec<u8>, Revert> {
		Self::call(address, input, env)
	}
}

impl<P: BuiltinPrecompile> PrimitivePrecompile for P {
	type T = <Self as BuiltinPrecompile>::T;
	const MATCHER: BuiltinAddressMatcher = P::MATCHER;
	const HAS_CONTRACT_INFO: bool = P::HAS_CONTRACT_INFO;

	fn call(
		address: &[u8; 20],
		input: &[u8],
		env: Option<&impl Ext<T = Self::T>>,
	) -> Result<Vec<u8>, Vec<u8>> {
		let call = <Self as BuiltinPrecompile>::Interface::abi_decode(input, true)
			.map_err(|_| Panic::from(PanicKind::Generic).abi_encode())?;
		match Self::call(address, &call, env) {
			Ok(value) => Ok(value),
			Err(err) => Err(err.abi_encode()),
		}
	}
}

#[impl_trait_for_tuples::impl_for_tuples(10)]
#[tuple_types_custom_trait_bound(PrimitivePrecompile<T=T>)]
impl<T: Config> Precompiles<T> for Tuple {
	const CHECK_COLLISION: () = {
		let matchers = [for_tuples!( #( Tuple::MATCHER ),* )];
		if BuiltinAddressMatcher::has_duplicates(&matchers) {
			panic!("Precompiles with duplicate matcher detected")
		}
	};

	fn kind(address: &[u8; 20]) -> Option<Kind> {
		let _ = <Self as Precompiles<T>>::CHECK_COLLISION;
		for_tuples!(
			#(
				if Tuple::MATCHER.matches(address) {
					if Tuple::HAS_CONTRACT_INFO {
						return Some(Kind::WithContractInfo)
					} else {
						return Some(Kind::NoContractInfo)
					}
				}
			)*
		);
		None
	}

	fn call(
		address: &[u8; 20],
		input: &[u8],
		env: &impl Ext<T = T>,
	) -> Option<Result<Vec<u8>, Vec<u8>>> {
		for_tuples!(
			#(
				if Tuple::MATCHER.matches(address) {
					let env = if Tuple::HAS_CONTRACT_INFO {
						Some(env)
					} else {
						None
					};
					return Some(Tuple::call(address, input, env));
				}
			)*
		);
		None
	}
}

impl<T: Config> Precompiles<T> for (Builtin<T>, <T as Config>::Precompiles) {
	const CHECK_COLLISION: () = ();

	fn kind(address: &[u8; 20]) -> Option<Kind> {
		<Builtin<T>>::kind(address).or_else(|| <T as Config>::Precompiles::kind(address))
	}

	fn call(
		address: &[u8; 20],
		input: &[u8],
		env: &impl Ext<T = T>,
	) -> Option<Result<Vec<u8>, Vec<u8>>> {
		<Builtin<T>>::call(address, input, env)
			.or_else(|| <T as Config>::Precompiles::call(address, input, env))
	}
}

impl AddressMatcher {
	const fn into_builtin(self) -> BuiltinAddressMatcher {
		match self {
			Self::Fixed(i) => BuiltinAddressMatcher::Fixed((i as u64) << 32),
			Self::Prefix(i) => BuiltinAddressMatcher::Prefix((i as u64) << 32),
		}
	}
}

impl BuiltinAddressMatcher {
	const fn suffix(&self) -> u64 {
		match self {
			Self::Fixed(i) => *i,
			Self::Prefix(i) => *i,
		}
	}

	const fn base_address(&self) -> [u8; 20] {
		let suffix = self.suffix().to_be_bytes();
		let mut address = [0u8; 20];
		let mut i = 12;
		while i < address.len() {
			address[i] = suffix[i - 12];
			i = i + 1;
		}
		address
	}

	const fn matches(&self, address: &[u8; 20]) -> bool {
		let base_address = self.base_address();
		let mut i = match self {
			Self::Fixed(_) => 0,
			Self::Prefix(_) => 4,
		};
		while i < base_address.len() {
			if address[i] != base_address[i] {
				return false
			}
			i = i + 1;
		}
		true
	}

	const fn has_duplicates(nums: &[Self]) -> bool {
		let len = nums.len();
		let mut i = 0;
		while i < len {
			let mut j = i + 1;
			while j < len {
				if nums[i].suffix() == nums[j].suffix() {
					return true;
				}
				j += 1;
			}
			i += 1;
		}
		false
	}
}
