use crate::{
	evm::{extract_revert_message, runtime::gas_from_weight, Bytes},
	ExecReturnValue, Weight,
};
use alloc::{string::String, vec::Vec};
use codec::{Decode, Encode};
use scale_info::TypeInfo;
use serde::{Deserialize, Serialize};
use sp_core::{H160, H256, U256};

/// Tracer configuration used to trace calls.
#[derive(TypeInfo, Debug, Clone, Encode, Decode, Serialize, Deserialize)]
pub enum TracerConfig {
	/// A tracer that captures call traces.
	CallTracer {
		/// Whether or not to capture logs.
		with_logs: bool,
	},
}
/// The type of call that was executed.
#[derive(
	Default, TypeInfo, Encode, Decode, Serialize, Deserialize, Eq, PartialEq, Clone, Debug,
)]
#[serde(rename_all = "UPPERCASE")]
pub enum CallType {
	/// A regular call.
	#[default]
	Call,
	/// A read-only call.
	StaticCall,
	/// A delegate call.
	DelegateCall,
}

/// The traces of a transaction.
#[derive(TypeInfo, Encode, Decode, Serialize, Deserialize, Clone, Debug, Eq, PartialEq)]
#[serde(untagged)]
pub enum Traces<Gas = Weight, Output = ExecReturnValue>
where
	Output: Default + PartialEq,
{
	/// The call traces captured during the transaction.
	CallTraces(Vec<CallTrace<Gas, Output>>),
}

/// The output and revert reason of an Ethereum trace.
#[derive(
	TypeInfo, Default, Encode, Decode, Serialize, Deserialize, Clone, Debug, Eq, PartialEq,
)]
pub struct EthOutput {
	/// The call output.
	pub output: Bytes,
	/// The revert reason, if the call reverted.
	#[serde(rename = "revertReason")]
	pub revert_reason: Option<String>,
}

impl From<ExecReturnValue> for EthOutput {
	fn from(value: ExecReturnValue) -> Self {
		Self {
			revert_reason: if value.did_revert() {
				extract_revert_message(&value.data)
			} else {
				None
			},
			output: Bytes(value.data),
		}
	}
}

/// The traces used in Ethereum debug RPC.
pub type EthTraces = Traces<U256, EthOutput>;

impl<Gas, Output: Default + PartialEq> Traces<Gas, Output> {
	/// Return mapped traces with the given gas mapper.
	pub fn map<T, V>(
		self,
		gas_mapper: impl Fn(Gas) -> T + Copy,
		output_mapper: impl Fn(Output) -> V + Copy,
	) -> Traces<T, V>
	where
		V: Default + PartialEq,
	{
		match self {
			Traces::CallTraces(traces) => Traces::CallTraces(
				traces.into_iter().map(|trace| trace.map(gas_mapper, output_mapper)).collect(),
			),
		}
	}
}

impl Traces {
	/// Return the traces as Ethereum traces.
	pub fn as_eth_traces<T: crate::Config>(self) -> EthTraces
	where
		crate::BalanceOf<T>: Into<U256>,
	{
		self.map(|weight| gas_from_weight::<T>(weight), |output| output.into())
	}
}

/// Return true if the value is the default value.
pub fn is_default<T: Default + PartialEq>(value: &T) -> bool {
	*value == T::default()
}

/// A smart contract execution call trace.
#[derive(
	TypeInfo, Default, Encode, Decode, Serialize, Deserialize, Clone, Debug, Eq, PartialEq,
)]
pub struct CallTrace<Gas = Weight, Output = ExecReturnValue>
where
	Output: Default + PartialEq,
{
	/// Address of the sender.
	pub from: H160,
	/// Address of the receiver.
	pub to: H160,
	/// Call input data.
	pub input: Vec<u8>,
	/// Amount of value transferred.
	#[serde(skip_serializing_if = "U256::is_zero")]
	pub value: U256,
	/// Type of call.
	#[serde(rename = "type")]
	pub call_type: CallType,
	/// Amount of gas provided for the call.
	pub gas: Gas,
	/// Amount of gas used.
	#[serde(rename = "gasUsed")]
	pub gas_used: Gas,
	/// Return data.
	#[serde(flatten, skip_serializing_if = "is_default")]
	pub output: Output,
	/// The error message if the call failed.
	#[serde(skip_serializing_if = "Option::is_none")]
	pub error: Option<String>,
	/// List of sub-calls.
	#[serde(skip_serializing_if = "Vec::is_empty")]
	pub calls: Vec<CallTrace<Gas, Output>>,
	/// List of logs emitted during the call.
	#[serde(skip_serializing_if = "Vec::is_empty")]
	pub logs: Vec<CallLog>,
}

/// A log emitted during a call.
#[derive(
	Debug, Default, Clone, Encode, Decode, TypeInfo, Serialize, Deserialize, Eq, PartialEq,
)]
pub struct CallLog {
	/// The address of the contract that emitted the log.
	pub address: H160,
	/// The log's data.
	#[serde(skip_serializing_if = "Bytes::is_empty")]
	pub data: Bytes,
	/// The topics used to index the log.
	#[serde(default, skip_serializing_if = "Vec::is_empty")]
	pub topics: Vec<H256>,
	/// Position of the log relative to subcalls within the same trace
	/// See <https://github.com/ethereum/go-ethereum/pull/28389> for details
	#[serde(with = "super::hex_serde")]
	pub position: u32,
}

impl<Gas, Output> CallTrace<Gas, Output>
where
	Output: Default + PartialEq,
{
	/// Return a new call gas with a mapped gas value.
	pub fn map<T, V>(
		self,
		gas_mapper: impl Fn(Gas) -> T + Copy,
		output_mapper: impl Fn(Output) -> V + Copy,
	) -> CallTrace<T, V>
	where
		V: Default + PartialEq,
	{
		CallTrace {
			from: self.from,
			to: self.to,
			input: self.input,
			value: self.value,
			call_type: self.call_type,
			error: self.error,
			gas: gas_mapper(self.gas),
			gas_used: gas_mapper(self.gas_used),
			output: output_mapper(self.output),
			calls: self.calls.into_iter().map(|call| call.map(gas_mapper, output_mapper)).collect(),
			logs: self.logs,
		}
	}
}

/// A transaction trace
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct TransactionTrace {
	/// The transaction hash.
	#[serde(rename = "txHash")]
	pub tx_hash: H256,
	/// The traces of the transaction.
	pub result: EthTraces,
}
