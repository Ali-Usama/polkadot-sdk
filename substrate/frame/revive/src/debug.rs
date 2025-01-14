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

use crate::{evm::TracerConfig, BalanceOf, Config, DispatchError, GasMeter, LOG_TARGET};
pub use crate::{
	evm::{CallLog, CallTrace, CallType, EthTraces, Traces},
	exec::{ExecResult, ExportedFunction},
	primitives::ExecReturnValue,
};
use alloc::{format, string::ToString, vec::Vec};
use sp_core::{H160, H256, U256};

/// Umbrella trait for all interfaces that serves for debugging.
pub trait Debugger<T: Config>: CallInterceptor<T> {}

impl<T: Config, V> Debugger<T> for V where V: CallInterceptor<T> {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tracer {
	LogTracer,
	CallTracer(CallTracer),
}

/// Defines methods to capture contract calls
pub trait Tracing<T: Config> {
	/// Called before a contract call is executed
	fn enter_child_span(
		&mut self,
		from: &H160,
		to: &H160,
		is_delegate_call: bool,
		is_read_only: bool,
		value: &U256,
		input: &[u8],
		gas_meter: &GasMeter<T>,
	);

	/// Record a log event
	fn log_event(&mut self, event: &H160, topics: &[H256], data: &[u8]);

	/// Called after a contract call is executed
	fn exit_child_span(&mut self, output: &ExecReturnValue, gas_meter: &GasMeter<T>);

	/// Called when a contract call terminates with an error
	fn exit_child_span_with_error(&mut self, error: DispatchError, gas_meter: &GasMeter<T>);
}

impl Tracer {
	/// Creates a new [`Tracer`] from the given config.
	pub fn from_config(config: TracerConfig) -> Self {
		match config {
			TracerConfig::CallTracer { with_logs } =>
				Tracer::CallTracer(CallTracer::new(with_logs)),
		}
	}

	/// Returns `true` if some traces have been collected.
	pub fn has_traces(&self) -> bool {
		match self {
			Tracer::CallTracer(tracer) => !tracer.traces.is_empty(),
			_ => false,
		}
	}

	/// Takes the traces collected by the tracer and resets them.
	pub fn collect_traces(&mut self) -> Traces {
		match self {
			Tracer::CallTracer(tracer) => {
				let traces = core::mem::take(&mut tracer.traces);
				Traces::CallTraces(traces)
			},
			Tracer::LogTracer => Traces::CallTraces(Default::default()),
		}
	}
}

impl<T: Config> Tracing<T> for Tracer
where
	BalanceOf<T>: Into<U256>,
{
	fn enter_child_span(
		&mut self,
		from: &H160,
		to: &H160,
		is_delegate_call: bool,
		is_read_only: bool,
		value: &U256,
		input: &[u8],
		gas_meter: &GasMeter<T>,
	) {
		match self {
			Tracer::CallTracer(tracer) => {
				<CallTracer as Tracing<T>>::enter_child_span(
					tracer,
					from,
					to,
					is_delegate_call,
					is_read_only,
					value,
					input,
					gas_meter,
				);
			},
			Tracer::LogTracer => {
				log::debug!(target: LOG_TARGET, "call (delegate: {is_delegate_call:?}, read_only: {is_read_only:?}) from: {from:?}, to: {to:?} value: {value:?}  input_data: {input:?}");
			},
		}
	}

	fn log_event(&mut self, event: &H160, topics: &[H256], data: &[u8]) {
		match self {
			Tracer::CallTracer(tracer) => {
				<CallTracer as Tracing<T>>::log_event(tracer, event, topics, data);
			},
			Tracer::LogTracer => {
				log::debug!(target: LOG_TARGET, "event {event:?} topics: {topics:?} data: {data:?}");
			},
		}
	}

	fn exit_child_span(&mut self, output: &ExecReturnValue, gas_meter: &GasMeter<T>) {
		match self {
			Tracer::CallTracer(tracer) => {
				<CallTracer as Tracing<T>>::exit_child_span(tracer, output, gas_meter);
			},
			Tracer::LogTracer => {
				log::debug!(target: LOG_TARGET, "call result {output:?}")
			},
		}
	}

	fn exit_child_span_with_error(&mut self, error: DispatchError, gas_meter: &GasMeter<T>) {
		match self {
			Tracer::CallTracer(tracer) => {
				<CallTracer as Tracing<T>>::exit_child_span_with_error(tracer, error, gas_meter);
			},
			Tracer::LogTracer => {
				log::debug!(target: LOG_TARGET, "call failed {error:?}")
			},
		}
	}
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct CallTracer {
	/// Store all in-progress CallTrace instances
	pub traces: Vec<CallTrace>,
	/// Stack of indices to the current active traces
	current_stack: Vec<usize>,
	/// whether or not to capture logs
	with_log: bool,
}

impl CallTracer {
	pub fn new(with_log: bool) -> Self {
		Self { traces: Vec::new(), current_stack: Vec::new(), with_log }
	}
}

impl<T: Config> Tracing<T> for CallTracer
where
	BalanceOf<T>: Into<U256>,
{
	fn enter_child_span(
		&mut self,
		from: &H160,
		to: &H160,
		is_delegate_call: bool,
		is_read_only: bool,
		value: &U256,
		input: &[u8],
		gas_meter: &GasMeter<T>,
	) {
		let call_type = if is_read_only {
			CallType::StaticCall
		} else if is_delegate_call {
			CallType::DelegateCall
		} else {
			CallType::Call
		};

		self.traces.push(CallTrace {
			from: *from,
			to: *to,
			value: (*value).into(),
			call_type,
			input: input.to_vec(),
			gas: gas_meter.gas_left(),
			..Default::default()
		});

		// Push the index onto the stack of the current active trace
		self.current_stack.push(self.traces.len() - 1);
	}

	fn log_event(&mut self, address: &H160, topics: &[H256], data: &[u8]) {
		if !self.with_log {
			return;
		}

		let current_index = self.current_stack.last().unwrap();
		let position = self.traces[*current_index].calls.len() as u32;
		let log = CallLog {
			address: *address,
			topics: topics.to_vec(),
			data: data.to_vec().into(),
			position,
		};

		let current_index = *self.current_stack.last().unwrap();
		self.traces[current_index].logs.push(log);
	}

	fn exit_child_span(&mut self, output: &ExecReturnValue, gas_meter: &GasMeter<T>) {
		// Set the output of the current trace
		let current_index = self.current_stack.pop().unwrap();
		let trace = &mut self.traces[current_index];
		trace.output = output.clone();
		trace.gas_used = gas_meter.gas_consumed();

		if output.did_revert() {
			trace.error = Some("execution reverted".to_string());
		}

		//  move the current trace into its parent
		if let Some(parent_index) = self.current_stack.last() {
			let child_trace = self.traces.remove(current_index);
			self.traces[*parent_index].calls.push(child_trace);
		}
	}
	fn exit_child_span_with_error(&mut self, error: DispatchError, gas_meter: &GasMeter<T>) {
		// Set the output of the current trace
		let current_index = self.current_stack.pop().unwrap();
		let trace = &mut self.traces[current_index];
		trace.gas_used = gas_meter.gas_consumed();

		trace.error = match error {
			DispatchError::Module(sp_runtime::ModuleError { message, .. }) =>
				Some(message.unwrap_or_default().to_string()),
			_ => Some(format!("{:?}", error)),
		};

		//  move the current trace into its parent
		if let Some(parent_index) = self.current_stack.last() {
			let child_trace = self.traces.remove(current_index);
			self.traces[*parent_index].calls.push(child_trace);
		}
	}
}

/// Provides an interface for intercepting contract calls.
pub trait CallInterceptor<T: Config> {
	/// Allows to intercept contract calls and decide whether they should be executed or not.
	/// If the call is intercepted, the mocked result of the call is returned.
	///
	/// # Arguments
	///
	/// * `contract_address` - The address of the contract that is about to be executed.
	/// * `entry_point` - Describes whether the call is the constructor or a regular call.
	/// * `input_data` - The raw input data of the call.
	///
	/// # Expected behavior
	///
	/// This method should return:
	/// * `Some(ExecResult)` - if the call should be intercepted and the mocked result of the call
	/// is returned.
	/// * `None` - otherwise, i.e. the call should be executed normally.
	fn intercept_call(
		_contract_address: &H160,
		_entry_point: ExportedFunction,
		_input_data: &[u8],
	) -> Option<ExecResult> {
		None
	}
}

impl<T: Config> CallInterceptor<T> for () {}
