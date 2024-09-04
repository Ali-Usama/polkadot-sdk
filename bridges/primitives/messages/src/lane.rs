// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Parity Bridges Common.

// Parity Bridges Common is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity Bridges Common is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity Bridges Common.  If not, see <http://www.gnu.org/licenses/>.

//! Primitives of messages module, that represents lane id.

use codec::{Decode, Encode, Error as CodecError, Input, MaxEncodedLen};
use frame_support::sp_runtime::Either;
use scale_info::TypeInfo;
use serde::{Deserialize, Serialize};
use sp_core::{RuntimeDebug, TypeId, H256};
use sp_io::hashing::blake2_256;

/// Bridge lane identifier.
///
/// Lane connects two endpoints at both sides of the bridge. We assume that every endpoint
/// has its own unique identifier. We want lane identifiers to be **the same on the both sides
/// of the bridge** (and naturally unique across global consensus if endpoints have unique
/// identifiers). So lane id is the hash (`blake2_256`) of **ordered** encoded locations
/// concatenation (separated by some binary data). I.e.:
///
/// ```nocompile
/// let endpoint1 = X2(GlobalConsensus(NetworkId::Rococo), Parachain(42));
/// let endpoint2 = X2(GlobalConsensus(NetworkId::Wococo), Parachain(777));
///
/// let final_lane_key = if endpoint1 < endpoint2 {
///     (endpoint1, VALUES_SEPARATOR, endpoint2)
/// } else {
///     (endpoint2, VALUES_SEPARATOR, endpoint1)
/// }.using_encoded(blake2_256);
/// ```
///
/// Note: For backwards compatibility reasons, we also handle the older format `[u8; 4]`.
#[derive(
	Clone,
	Copy,
	Decode,
	Encode,
	Eq,
	Ord,
	PartialOrd,
	PartialEq,
	TypeInfo,
	MaxEncodedLen,
	Serialize,
	Deserialize,
)]
pub struct LaneId(InnerLaneId);

impl LaneId {
	/// Create lane identifier from two locations.
	pub fn new<T: Ord + Encode>(endpoint1: T, endpoint2: T) -> Self {
		const VALUES_SEPARATOR: [u8; 31] = *b"bridges-lane-id-value-separator";

		LaneId(InnerLaneId::Hash(
			if endpoint1 < endpoint2 {
				(endpoint1, VALUES_SEPARATOR, endpoint2)
			} else {
				(endpoint2, VALUES_SEPARATOR, endpoint1)
			}
			.using_encoded(blake2_256)
			.into(),
		))
	}

	/// Create lane identifier from given hash.
	///
	/// There's no `From<H256>` implementation for the `LaneId`, because using this conversion
	/// in a wrong way (i.e. computing hash of endpoints manually) may lead to issues. So we
	/// want the call to be explicit.
	pub const fn from_inner(inner: Either<H256, [u8; 4]>) -> Self {
		LaneId(match inner {
			Either::Left(hash) => InnerLaneId::Hash(hash),
			Either::Right(array) => InnerLaneId::Array(array),
		})
	}

	/// Access the inner lane representation.
	pub fn inner(&self) -> Either<&H256, &[u8; 4]> {
		match &self.0 {
			InnerLaneId::Array(array) => Either::Right(array),
			InnerLaneId::Hash(hash) => Either::Left(hash),
		}
	}
}

impl core::fmt::Display for LaneId {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		core::fmt::Display::fmt(&self.0, f)
	}
}

impl core::fmt::Debug for LaneId {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		core::fmt::Debug::fmt(&self.0, f)
	}
}

impl TypeId for LaneId {
	const TYPE_ID: [u8; 4] = *b"blan";
}

#[derive(Clone, Copy, Eq, Ord, PartialOrd, PartialEq, TypeInfo, Serialize, Deserialize)]
enum InnerLaneId {
	/// New format 32-byte hash generated by `blake2_256`.
	Hash(H256),
	/// Old format (for backwards compatibility).
	Array([u8; 4]),
}

// Prefix used to differentiate `LaneId` for backward compatibility.
// Hex value: `48615368`
const INNER_LANE_ID_AS_HASH_PREFIX: &[u8; 4] = b"HaSh";

impl MaxEncodedLen for InnerLaneId {
	fn max_encoded_len() -> usize {
		INNER_LANE_ID_AS_HASH_PREFIX
			.encoded_size()
			.saturating_add(H256::max_encoded_len())
	}
}

impl Encode for InnerLaneId {
	fn encode(&self) -> sp_std::vec::Vec<u8> {
		match self {
			InnerLaneId::Hash(hash) => {
				// prefix new hash, so we can easily decode
				(INNER_LANE_ID_AS_HASH_PREFIX, hash).encode()
			},
			InnerLaneId::Array(array) => {
				// encode backwards compatible
				array.encode()
			},
		}
	}
}

impl Decode for InnerLaneId {
	fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
		// read 4 bytes first
		let prefix_or_array: [u8; 4] = Decode::decode(input)?;

		// if matches prefix, it is a new format
		if prefix_or_array.eq(INNER_LANE_ID_AS_HASH_PREFIX) {
			// now read more 32 bytes for hash
			return H256::decode(input).map(InnerLaneId::Hash)
		}

		// return prefix `[u8; 4]` for backwards compatibly as a best effort
		Ok(InnerLaneId::Array(prefix_or_array))
	}
}

impl core::fmt::Display for InnerLaneId {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		match self {
			InnerLaneId::Array(array) => write!(f, "InnerLaneId::Array({:?})", array),
			InnerLaneId::Hash(hash) => write!(f, "InnerLaneId::Hash({:?})", hash),
		}
	}
}

impl core::fmt::Debug for InnerLaneId {
	fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
		match self {
			InnerLaneId::Array(array) => array.fmt(fmt),
			InnerLaneId::Hash(hash) => hash.fmt(fmt),
		}
	}
}

/// The representation of `LaneId`'s inner bytes.
#[derive(Clone, Encode, Decode, RuntimeDebug, PartialEq, Eq, TypeInfo)]
pub struct LaneIdBytes(sp_std::vec::Vec<u8>);
impl From<LaneId> for LaneIdBytes {
	fn from(lane_id: LaneId) -> Self {
		match lane_id.inner() {
			Either::Left(hash) => Self(hash.as_bytes().to_vec()),
			Either::Right(array) => Self(array.to_vec()),
		}
	}
}

/// Lane state.
#[derive(Clone, Copy, Decode, Encode, Eq, PartialEq, TypeInfo, MaxEncodedLen, RuntimeDebug)]
pub enum LaneState {
	/// Lane is opened and messages may be sent/received over it.
	Opened,
	/// Lane is closed and all attempts to send/receive messages to/from this lane
	/// will fail.
	///
	/// Keep in mind that the lane has two ends and the state of the same lane at
	/// its ends may be different. Those who are controlling/serving the lane
	/// and/or sending messages over the lane, have to coordinate their actions on
	/// both ends to make sure that lane is operating smoothly on both ends.
	Closed,
}

impl LaneState {
	/// Returns true if lane state allows sending/receiving messages.
	pub fn is_active(&self) -> bool {
		matches!(*self, LaneState::Opened)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::MessageNonce;

	#[test]
	fn lane_id_debug_format_matches_inner_hash_format() {
		assert_eq!(
			format!("{:?}", LaneId(InnerLaneId::Hash(H256::from([1u8; 32])))),
			format!("{:?}", H256::from([1u8; 32])),
		);
		assert_eq!(
			format!("{:?}", LaneId(InnerLaneId::Array([0, 0, 0, 1]))),
			format!("{:?}", [0, 0, 0, 1]),
		);
	}

	#[test]
	fn encode_decode_works() {
		// simple encode/decode - new format
		let lane_id = LaneId(InnerLaneId::Hash(H256::from([1u8; 32])));
		let encoded_lane_id = lane_id.encode();
		let decoded_lane_id = LaneId::decode(&mut &encoded_lane_id[..]).expect("decodable");
		assert_eq!(lane_id, decoded_lane_id);
		assert_eq!(
			"486153680101010101010101010101010101010101010101010101010101010101010101",
			hex::encode(encoded_lane_id)
		);

		// simple encode/decode - old format
		let lane_id = LaneId(InnerLaneId::Array([0, 0, 0, 1]));
		let encoded_lane_id = lane_id.encode();
		let decoded_lane_id = LaneId::decode(&mut &encoded_lane_id[..]).expect("decodable");
		assert_eq!(lane_id, decoded_lane_id);
		assert_eq!("00000001", hex::encode(encoded_lane_id));

		// decode sample
		let bytes = vec![0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0];
		let (lane, nonce_start, nonce_end): (LaneId, MessageNonce, MessageNonce) =
			Decode::decode(&mut &bytes[..]).unwrap();
		assert_eq!(lane, LaneId(InnerLaneId::Array([0, 0, 0, 2])));
		assert_eq!(nonce_start, 1);
		assert_eq!(nonce_end, 1);

		// run encode/decode for `LaneId` with different positions
		let test_data = vec![
			(LaneId(InnerLaneId::Array([0, 0, 0, 1])), 1088_u64, 9185_u64),
			(LaneId(InnerLaneId::Hash(H256::from([1u8; 32]))), 1088_u64, 9185_u64),
		];
		for (expected_lane, expected_nonce_start, expected_nonce_end) in test_data {
			// decode: LaneId,Nonce,Nonce
			let bytes = (expected_lane, expected_nonce_start, expected_nonce_end).encode();
			let (lane, nonce_start, nonce_end): (LaneId, MessageNonce, MessageNonce) =
				Decode::decode(&mut &bytes[..]).unwrap();
			assert_eq!(lane, expected_lane);
			assert_eq!(nonce_start, expected_nonce_start);
			assert_eq!(nonce_end, expected_nonce_end);

			// decode: Nonce,LaneId,Nonce
			let bytes = (expected_nonce_start, expected_lane, expected_nonce_end).encode();
			let (nonce_start, lane, nonce_end): (MessageNonce, LaneId, MessageNonce) =
				Decode::decode(&mut &bytes[..]).unwrap();
			assert_eq!(lane, expected_lane);
			assert_eq!(nonce_start, expected_nonce_start);
			assert_eq!(nonce_end, expected_nonce_end);

			// decode: Nonce,Nonce,LaneId
			let bytes = (expected_nonce_start, expected_nonce_end, expected_lane).encode();
			let (nonce_start, nonce_end, lane): (MessageNonce, MessageNonce, LaneId) =
				Decode::decode(&mut &bytes[..]).unwrap();
			assert_eq!(lane, expected_lane);
			assert_eq!(nonce_start, expected_nonce_start);
			assert_eq!(nonce_end, expected_nonce_end);
		}
	}

	#[test]
	fn lane_id_bytes_works() {
		let lane_id_bytes: LaneIdBytes = LaneId(InnerLaneId::Array([0, 0, 0, 1])).into();
		assert_eq!("00000001", hex::encode(lane_id_bytes.0));

		let lane_id_bytes: LaneIdBytes = LaneId(InnerLaneId::Hash(H256::from([1u8; 32]))).into();
		assert_eq!(
			"0101010101010101010101010101010101010101010101010101010101010101",
			hex::encode(lane_id_bytes.0)
		);
	}

	#[test]
	fn lane_id_is_generated_using_ordered_endpoints() {
		assert_eq!(LaneId::new(1, 2), LaneId::new(2, 1));
	}

	#[test]
	fn lane_id_is_different_for_different_endpoints() {
		assert_ne!(LaneId::new(1, 2), LaneId::new(1, 3));
	}

	#[test]
	fn lane_id_is_different_even_if_arguments_has_partial_matching_encoding() {
		/// Some artificial type that generates the same encoding for different values
		/// concatenations. I.e. the encoding for `(Either::Two(1, 2), Either::Two(3, 4))`
		/// is the same as encoding of `(Either::Three(1, 2, 3), Either::One(4))`.
		/// In practice, this type is not useful, because you can't do a proper decoding.
		/// But still there may be some collisions even in proper types.
		#[derive(Eq, Ord, PartialEq, PartialOrd)]
		enum Either {
			Three(u64, u64, u64),
			Two(u64, u64),
			One(u64),
		}

		impl codec::Encode for Either {
			fn encode(&self) -> Vec<u8> {
				match *self {
					Self::One(a) => a.encode(),
					Self::Two(a, b) => (a, b).encode(),
					Self::Three(a, b, c) => (a, b, c).encode(),
				}
			}
		}

		assert_ne!(
			LaneId::new(Either::Two(1, 2), Either::Two(3, 4)),
			LaneId::new(Either::Three(1, 2, 3), Either::One(4)),
		);
	}
}
