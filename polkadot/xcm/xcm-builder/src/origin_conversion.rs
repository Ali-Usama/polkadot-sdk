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

//! Various implementations for `ConvertOrigin`.

use core::marker::PhantomData;
use frame_support::traits::{EnsureOrigin, Get, GetBacking, OriginTrait};
use frame_system::RawOrigin as SystemRawOrigin;
use polkadot_parachain_primitives::primitives::IsSystem;
use sp_runtime::traits::TryConvert;
use xcm::latest::{BodyId, BodyPart, Junction, Junctions::*, Location, NetworkId, OriginKind};
use xcm_executor::traits::{ConvertLocation, ConvertOrigin};

/// Sovereign accounts use the system's `Signed` origin with an account ID derived from the
/// `LocationConverter`.
pub struct SovereignSignedViaLocation<LocationConverter, RuntimeOrigin>(
	PhantomData<(LocationConverter, RuntimeOrigin)>,
);
impl<LocationConverter: ConvertLocation<RuntimeOrigin::AccountId>, RuntimeOrigin: OriginTrait>
	ConvertOrigin<RuntimeOrigin> for SovereignSignedViaLocation<LocationConverter, RuntimeOrigin>
where
	RuntimeOrigin::AccountId: Clone,
{
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(
			target: "xcm::origin_conversion",
			"SovereignSignedViaLocation origin: {:?}, kind: {:?}",
			origin, kind,
		);
		if let OriginKind::SovereignAccount = kind {
			let location = LocationConverter::convert_location(&origin).ok_or(origin)?;
			Ok(RuntimeOrigin::signed(location).into())
		} else {
			Err(origin)
		}
	}
}

pub struct ParentAsSuperuser<RuntimeOrigin>(PhantomData<RuntimeOrigin>);
impl<RuntimeOrigin: OriginTrait> ConvertOrigin<RuntimeOrigin> for ParentAsSuperuser<RuntimeOrigin> {
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(target: "xcm::origin_conversion", "ParentAsSuperuser origin: {:?}, kind: {:?}", origin, kind);
		if kind == OriginKind::Superuser && origin.contains_parents_only(1) {
			Ok(RuntimeOrigin::root())
		} else {
			Err(origin)
		}
	}
}

pub struct ChildSystemParachainAsSuperuser<ParaId, RuntimeOrigin>(
	PhantomData<(ParaId, RuntimeOrigin)>,
);
impl<ParaId: IsSystem + From<u32>, RuntimeOrigin: OriginTrait> ConvertOrigin<RuntimeOrigin>
	for ChildSystemParachainAsSuperuser<ParaId, RuntimeOrigin>
{
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(target: "xcm::origin_conversion", "ChildSystemParachainAsSuperuser origin: {:?}, kind: {:?}", origin, kind);
		match (kind, origin.unpack()) {
			(OriginKind::Superuser, (0, [Junction::Parachain(id)]))
				if ParaId::from(*id).is_system() =>
			{
				Ok(RuntimeOrigin::root())
			},
			_ => Err(origin),
		}
	}
}

pub struct SiblingSystemParachainAsSuperuser<ParaId, RuntimeOrigin>(
	PhantomData<(ParaId, RuntimeOrigin)>,
);
impl<ParaId: IsSystem + From<u32>, RuntimeOrigin: OriginTrait> ConvertOrigin<RuntimeOrigin>
	for SiblingSystemParachainAsSuperuser<ParaId, RuntimeOrigin>
{
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(
			target: "xcm::origin_conversion",
			"SiblingSystemParachainAsSuperuser origin: {:?}, kind: {:?}",
			origin, kind,
		);
		match (kind, origin.unpack()) {
			(OriginKind::Superuser, (1, [Junction::Parachain(id)]))
				if ParaId::from(*id).is_system() =>
			{
				Ok(RuntimeOrigin::root())
			},
			_ => Err(origin),
		}
	}
}

pub struct ChildParachainAsNative<ParachainOrigin, RuntimeOrigin>(
	PhantomData<(ParachainOrigin, RuntimeOrigin)>,
);
impl<ParachainOrigin: From<u32>, RuntimeOrigin: From<ParachainOrigin>> ConvertOrigin<RuntimeOrigin>
	for ChildParachainAsNative<ParachainOrigin, RuntimeOrigin>
{
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(target: "xcm::origin_conversion", "ChildParachainAsNative origin: {:?}, kind: {:?}", origin, kind);
		match (kind, origin.unpack()) {
			(OriginKind::Native, (0, [Junction::Parachain(id)])) => {
				Ok(RuntimeOrigin::from(ParachainOrigin::from(*id)))
			},
			_ => Err(origin),
		}
	}
}

pub struct SiblingParachainAsNative<ParachainOrigin, RuntimeOrigin>(
	PhantomData<(ParachainOrigin, RuntimeOrigin)>,
);
impl<ParachainOrigin: From<u32>, RuntimeOrigin: From<ParachainOrigin>> ConvertOrigin<RuntimeOrigin>
	for SiblingParachainAsNative<ParachainOrigin, RuntimeOrigin>
{
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(
			target: "xcm::origin_conversion",
			"SiblingParachainAsNative origin: {:?}, kind: {:?}",
			origin, kind,
		);
		match (kind, origin.unpack()) {
			(OriginKind::Native, (1, [Junction::Parachain(id)])) => {
				Ok(RuntimeOrigin::from(ParachainOrigin::from(*id)))
			},
			_ => Err(origin),
		}
	}
}

// Our Relay-chain has a native origin given by the `Get`ter.
pub struct RelayChainAsNative<RelayOrigin, RuntimeOrigin>(
	PhantomData<(RelayOrigin, RuntimeOrigin)>,
);
impl<RelayOrigin: Get<RuntimeOrigin>, RuntimeOrigin> ConvertOrigin<RuntimeOrigin>
	for RelayChainAsNative<RelayOrigin, RuntimeOrigin>
{
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(target: "xcm::origin_conversion", "RelayChainAsNative origin: {:?}, kind: {:?}", origin, kind);
		if kind == OriginKind::Native && origin.contains_parents_only(1) {
			Ok(RelayOrigin::get())
		} else {
			Err(origin)
		}
	}
}

pub struct SignedAccountId32AsNative<Network, RuntimeOrigin>(PhantomData<(Network, RuntimeOrigin)>);
impl<Network: Get<Option<NetworkId>>, RuntimeOrigin: OriginTrait> ConvertOrigin<RuntimeOrigin>
	for SignedAccountId32AsNative<Network, RuntimeOrigin>
where
	RuntimeOrigin::AccountId: From<[u8; 32]>,
{
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(
			target: "xcm::origin_conversion",
			"SignedAccountId32AsNative origin: {:?}, kind: {:?}",
			origin, kind,
		);
		match (kind, origin.unpack()) {
			(OriginKind::Native, (0, [Junction::AccountId32 { id, network }]))
				if matches!(network, None) || *network == Network::get() =>
			{
				Ok(RuntimeOrigin::signed((*id).into()))
			},
			_ => Err(origin),
		}
	}
}

pub struct SignedAccountKey20AsNative<Network, RuntimeOrigin>(
	PhantomData<(Network, RuntimeOrigin)>,
);
impl<Network: Get<Option<NetworkId>>, RuntimeOrigin: OriginTrait> ConvertOrigin<RuntimeOrigin>
	for SignedAccountKey20AsNative<Network, RuntimeOrigin>
where
	RuntimeOrigin::AccountId: From<[u8; 20]>,
{
	fn convert_origin(
		origin: impl Into<Location>,
		kind: OriginKind,
	) -> Result<RuntimeOrigin, Location> {
		let origin = origin.into();
		log::trace!(
			target: "xcm::origin_conversion",
			"SignedAccountKey20AsNative origin: {:?}, kind: {:?}",
			origin, kind,
		);
		match (kind, origin.unpack()) {
			(OriginKind::Native, (0, [Junction::AccountKey20 { key, network }]))
				if (matches!(network, None) || *network == Network::get()) =>
			{
				Ok(RuntimeOrigin::signed((*key).into()))
			},
			_ => Err(origin),
		}
	}
}

/// `EnsureOrigin` barrier to convert from dispatch origin to XCM origin, if one exists.
pub struct EnsureXcmOrigin<RuntimeOrigin, Conversion>(PhantomData<(RuntimeOrigin, Conversion)>);
impl<RuntimeOrigin: OriginTrait + Clone, Conversion: TryConvert<RuntimeOrigin, Location>>
	EnsureOrigin<RuntimeOrigin> for EnsureXcmOrigin<RuntimeOrigin, Conversion>
where
	RuntimeOrigin::PalletsOrigin: PartialEq,
{
	type Success = Location;
	fn try_origin(o: RuntimeOrigin) -> Result<Self::Success, RuntimeOrigin> {
		let o = match Conversion::try_convert(o) {
			Ok(location) => return Ok(location),
			Err(o) => o,
		};
		// We institute a root fallback so root can always represent the context. This
		// guarantees that `successful_origin` will work.
		if o.caller() == RuntimeOrigin::root().caller() {
			Ok(Here.into())
		} else {
			Err(o)
		}
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<RuntimeOrigin, ()> {
		Ok(RuntimeOrigin::root())
	}
}

/// `Convert` implementation to convert from some a `Signed` (system) `Origin` into an
/// `AccountId32`.
///
/// Typically used when configuring `pallet-xcm` for allowing normal accounts to dispatch an XCM
/// from an `AccountId32` origin.
pub struct SignedToAccountId32<RuntimeOrigin, AccountId, Network>(
	PhantomData<(RuntimeOrigin, AccountId, Network)>,
);
impl<
		RuntimeOrigin: OriginTrait + Clone,
		AccountId: Into<[u8; 32]>,
		Network: Get<Option<NetworkId>>,
	> TryConvert<RuntimeOrigin, Location> for SignedToAccountId32<RuntimeOrigin, AccountId, Network>
where
	RuntimeOrigin::PalletsOrigin: From<SystemRawOrigin<AccountId>>
		+ TryInto<SystemRawOrigin<AccountId>, Error = RuntimeOrigin::PalletsOrigin>,
{
	fn try_convert(o: RuntimeOrigin) -> Result<Location, RuntimeOrigin> {
		o.try_with_caller(|caller| match caller.try_into() {
			Ok(SystemRawOrigin::Signed(who)) => {
				Ok(Junction::AccountId32 { network: Network::get(), id: who.into() }.into())
			},
			Ok(other) => Err(other.into()),
			Err(other) => Err(other),
		})
	}
}

/// `Convert` implementation to convert from some an origin which implements `Backing` into a
/// corresponding `Plurality` `Location`.
///
/// Typically used when configuring `pallet-xcm` for allowing a collective's Origin to dispatch an
/// XCM from a `Plurality` origin.
pub struct BackingToPlurality<RuntimeOrigin, COrigin, Body>(
	PhantomData<(RuntimeOrigin, COrigin, Body)>,
);
impl<RuntimeOrigin: OriginTrait + Clone, COrigin: GetBacking, Body: Get<BodyId>>
	TryConvert<RuntimeOrigin, Location> for BackingToPlurality<RuntimeOrigin, COrigin, Body>
where
	RuntimeOrigin::PalletsOrigin:
		From<COrigin> + TryInto<COrigin, Error = RuntimeOrigin::PalletsOrigin>,
{
	fn try_convert(o: RuntimeOrigin) -> Result<Location, RuntimeOrigin> {
		o.try_with_caller(|caller| match caller.try_into() {
			Ok(co) => match co.get_backing() {
				Some(backing) => Ok(Junction::Plurality {
					id: Body::get(),
					part: BodyPart::Fraction { nom: backing.approvals, denom: backing.eligible },
				}
				.into()),
				None => Err(co.into()),
			},
			Err(other) => Err(other),
		})
	}
}

/// `Convert` implementation to convert from an origin which passes the check of an `EnsureOrigin`
/// into a voice of a given pluralistic `Body`.
pub struct OriginToPluralityVoice<RuntimeOrigin, EnsureBodyOrigin, Body>(
	PhantomData<(RuntimeOrigin, EnsureBodyOrigin, Body)>,
);
impl<RuntimeOrigin: Clone, EnsureBodyOrigin: EnsureOrigin<RuntimeOrigin>, Body: Get<BodyId>>
	TryConvert<RuntimeOrigin, Location>
	for OriginToPluralityVoice<RuntimeOrigin, EnsureBodyOrigin, Body>
{
	fn try_convert(o: RuntimeOrigin) -> Result<Location, RuntimeOrigin> {
		match EnsureBodyOrigin::try_origin(o) {
			Ok(_) => Ok(Junction::Plurality { id: Body::get(), part: BodyPart::Voice }.into()),
			Err(o) => Err(o),
		}
	}
}
