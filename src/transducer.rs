use std::{
	collections::{HashMap, HashSet, VecDeque},
	fmt::Display,
};

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Transducer for fast text-to-text transformation without backtracking.
///
/// To create a transducer use a [`Builder`].
///
/// At any given point in the input, the transducer will try to match the
/// longest possible valid input sequence and generate the respective output
/// text.
///
/// If no output matches at the current position, the transducer will output
/// a single input character and try again from the next position.
#[derive(Debug)]
pub struct Transducer {
	start: usize,
	program: Vec<Op>,
}

impl Transducer {
	/// Parse a string and returns the transformed output.
	///
	/// This is just a helper wrapper for [`Transducer::parse`].
	pub fn parse_str<S: AsRef<str>>(&self, input: S) -> String {
		self.parse(input.as_ref().chars()).collect()
	}

	/// Parse the input characters and returns the transformed output one
	/// character at a time using an [`Iterator`].
	pub fn parse<'a, S: IntoIterator<Item = char>>(&'a self, input: S) -> TransducerIter<'a, S::IntoIter> {
		TransducerIter {
			parent: self,
			input: input.into_iter(),
			counter: self.start,
			current: None,
		}
	}

	/// Returns a [`TokenStream`] containing rust code equivalent to the
	/// transducer.
	///
	/// This is meant to be used by a `proc_macro` to generate a transducer
	/// as raw rust code.
	///
	/// The generated code is meant to be used inside a module defined by the
	/// caller. The generated module contains two public symbols: `Transducer`
	/// and `new`.
	///
	/// `Transducer` is a struct and `new` is a generic constructor function
	/// with type `fn(T) -> Transducer`, where `T` is [`IntoIterator<Item=char>`].
	///
	/// The `Transducer` holds the input as an [`Iterator<Item=char>`] and
	/// itself implements an [`Iterator`] that generates the output chars.
	pub fn to_tokens(&self) -> TokenStream {
		let state_name = |n: usize| {
			let name = format_ident!("State{}", n);
			name
		};

		let state_id = |n: usize| {
			let name = state_name(n);
			quote! { _S :: #name }
		};

		let start = state_id(self.start);

		let mut states = Vec::new();
		let program: Vec<_> = self
			.program
			.iter()
			.enumerate()
			.map(|(index, op)| {
				let is_start = index == self.start;

				// segment of code to read the next input to `input`
				let read_input = quote! {
					let input = if let Some(char) = self.next {
						self.next = None;
						Some(char)
					} else {
						self.iter.next()
					};
				};
				let read_input = if is_start {
					quote! {
						#read_input
						if input.is_none() {
							self.state = _S::End;
							return None;
						}
					}
				} else {
					read_input
				};

				// segment of code to undo the last input read
				let undo_input = quote! {
					self.next = input;
				};

				// generate the code for a transition action
				let action = |action: Action| match action {
					Action::Char(char) => {
						if index == self.start {
							quote! {
								return Some(#char);
							}
						} else {
							quote! {
								self.state = #start;
								return Some(#char);
							}
						}
					}
					Action::Next(next) => {
						if next == index {
							quote! {}
						} else {
							let next = state_id(next);
							quote! {
								self.state = #next;
							}
						}
					}
				};

				// generate the code for the current operation

				let current = state_id(index);
				let current_name = state_name(index);
				states.push(quote! { #current_name });
				let op = match op {
					&Op::Char => {
						quote! {
							#read_input
							self.state = #start;
							return input;
						}
					}
					&Op::Jump { next } => {
						let next = state_id(next);
						quote! {
							self.state = #next;
						}
					}
					&Op::Push { char, next } => {
						let next = state_id(next);
						quote! {
							self.state = #next;
							return Some(#char);
						}
					}
					&Op::Read { char, next, fail } => {
						let next = action(next);
						let fail = action(fail);
						quote! {
							#read_input
							if input == Some(#char) {
								#next
							} else {
								#undo_input
								#fail
							};
						}
					}
					Op::Test { table, fail } => {
						let fail = action(*fail);
						let mut next = table.iter().collect::<Vec<_>>();
						next.sort();
						let next = next
							.into_iter()
							.map(|(char, next)| {
								let next = action(*next);
								quote! {
									Some(#char) => { #next }
								}
							})
							.collect::<Vec<_>>();
						quote! {
							#read_input
							match input {
								#( #next )*
								input => {
									#undo_input
									#fail
								}
							}
						}
					}
				};
				quote! {
					#current => { #op }
				}
			})
			.collect();

		quote! {
			use ::std::iter::Iterator;
			use ::std::option::Option;

			#[derive(Copy, Clone)]
			enum _S {
				#( #states, )*
				End,
			}

			#[doc = r#"
				Transducer that applies transformation rules to the input text.

				The transducer takes the input as an [`Iterator<Item=char>`] and
				implements that same trait to generate the output.

				This is generated as raw rust code by a proc-macro.
			"#]
			pub struct Transducer<I: Iterator<Item = char>> {
				state: _S,
				iter: I,
				next: Option<char>,
			}

			impl<I: Iterator<Item = char>> Iterator for Transducer<I> {
				type Item = char;

				fn next(&mut self) -> Option<Self::Item> {
					loop {
						match self.state {
							#( #program )*
							_S::End => {
								return None;
							}
						}
					}
				}
			}

			#[doc = r#"
				Returns a new [`Transducer`] for the given input iterator.

				The returned transducer implements [`Iterator<Item=char>`]
				consuming the input characters one at a time and generating
				the transformed output.
			"#]
			pub fn new<I: IntoIterator<Item = char>>(input: I) -> Transducer<I::IntoIter> {
				Transducer { state: #start, iter: input.into_iter(), next: None }
			}
		}
	}
}

impl std::fmt::Display for Transducer {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		writeln!(f, "Transducer(start = {}) {{", self.start)?;
		for (n, op) in self.program.iter().enumerate() {
			let op: String = format!("{}", op)
				.split('\n')
				.enumerate()
				.map(|(n, line)| format!("{}{}\n", if n > 0 { "        " } else { "" }, line))
				.collect();
			write!(f, "  {:04}: {}", n, op)?;
		}
		write!(f, "}}")?;
		Ok(())
	}
}

/// Iterator for [`Transducer`].
pub struct TransducerIter<'a, S: Iterator<Item = char>> {
	parent: &'a Transducer,
	input: S,
	counter: usize,
	current: Option<char>,
}

impl<'a, S: Iterator<Item = char>> Iterator for TransducerIter<'a, S> {
	type Item = char;

	fn next(&mut self) -> Option<Self::Item> {
		let program = &self.parent.program;
		let start = self.parent.start;
		loop {
			match &program[self.counter] {
				Op::Test { table, fail } => {
					let next_input = self.read();
					if let Some(next_input) = next_input {
						if let Some(next) = table.get(&next_input) {
							match next {
								Action::Next(next) => {
									self.counter = *next;
								}
								Action::Char(char) => {
									self.counter = start;
									return Some(*char);
								}
							}
						} else {
							self.current = Some(next_input);
							match fail {
								Action::Next(fail) => {
									self.counter = *fail;
								}
								Action::Char(char) => {
									self.counter = start;
									return Some(*char);
								}
							}
						}
					} else {
						self.current = None;
						match fail {
							Action::Next(fail) => {
								self.counter = *fail;
							}
							Action::Char(char) => {
								self.counter = start;
								return Some(*char);
							}
						}
					}
				}
				Op::Read { char, next, fail } => {
					let next_input = self.read();
					if let Some(next_input) = next_input {
						if next_input == *char {
							match next {
								Action::Next(next) => {
									self.counter = *next;
								}
								Action::Char(char) => {
									self.counter = start;
									return Some(*char);
								}
							}
						} else {
							self.current = Some(next_input);
							match fail {
								Action::Next(fail) => {
									self.counter = *fail;
								}
								Action::Char(char) => {
									self.counter = start;
									return Some(*char);
								}
							}
						}
					} else {
						self.current = None;
						match fail {
							Action::Next(fail) => {
								self.counter = *fail;
							}
							Action::Char(char) => {
								self.counter = start;
								return Some(*char);
							}
						}
					}
				}
				Op::Push { char, next } => {
					self.counter = *next;
					return Some(*char);
				}
				Op::Char => {
					self.counter = self.parent.start;
					return self.read();
				}
				Op::Jump { next } => {
					self.counter = *next;
				}
			}
		}
	}
}

impl<'a, S: Iterator<Item = char>> TransducerIter<'a, S> {
	fn read(&mut self) -> Option<char> {
		self.current.take().or_else(|| self.input.next())
	}
}

/// Transducer operation.
#[derive(Debug)]
enum Op {
	/// Outputs a single character and moves to the next operation.
	Push { char: char, next: usize },
	/// Tries to read the given char from input. Moves to `next` if successful,
	/// otherwise moves to `fail`.
	Read { char: char, next: Action, fail: Action },
	/// Test the next input character against the given table. Moves to the
	/// corresponding operation if successful, otherwise moves to `fail`.
	Test { table: HashMap<char, Action>, fail: Action },
	/// Unconditional jump to the given operation.
	Jump { next: usize },
	/// Emits the current input character and resets.
	Char,
}

/// Represents a transition action for an [`Op`].
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
enum Action {
	/// Moves to the given state.
	Next(usize),
	/// Generates a single output character and reset. This is specifically
	/// to optimize the common case of outputing a single character.
	Char(char),
}

impl Display for Action {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			&Action::Char(char) => write!(f, "'{}'", char),
			&Action::Next(next) => write!(f, "{:04}", next),
		}
	}
}

impl Display for Op {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Op::Push { char, next } => write!(f, "PUSH '{}' THEN {:04}", char, next),
			Op::Read { char, next, fail } => write!(f, "READ '{}': {:04} ELSE {:04}", char, next, fail),
			Op::Jump { next } => write!(f, "JUMP {:04}", next),
			Op::Char => write!(f, "CHAR"),
			Op::Test { table, fail } => {
				writeln!(f, "TEST:")?;

				let mut entries: Vec<_> = table.iter().collect();
				entries.sort();
				for (char, next) in entries.into_iter() {
					writeln!(f, "| '{}': {:04}", char, next)?;
				}
				write!(f, "|  * : {:04}", fail)
			}
		}
	}
}

//----------------------------------------------------------------------------//
// Builder
//----------------------------------------------------------------------------//

/// Builder for a [`Transducer`].
#[derive(Debug, Clone)]
pub struct Builder {
	states: Vec<BuilderState>,
}

// TODO: optimize jumps from matching states to states that generate a single
// character and revert to the initial state

impl Builder {
	/// Returns a new empty [`Builder`] instance.
	pub fn new() -> Builder {
		let mut out = Builder { states: Vec::new() };
		out.states.push(BuilderState::new());
		out
	}

	/// Add a transformation from the input string to the output.
	///
	/// `input` must not be empty.
	pub fn add<S1: AsRef<str>, S2: AsRef<str>>(&mut self, input: S1, output: S2) {
		let input = input.as_ref();
		let output = output.as_ref();
		if input.len() == 0 {
			panic!("Builder::add: transducer input sequence cannot be empty");
		}

		let mut current = 0;
		for char in input.chars() {
			let next_entry = self.states.len();
			let entry = { *self.states[current].next.entry(char).or_insert(next_entry) };
			if entry == next_entry {
				self.states.push(BuilderState::new());
			}
			current = entry;
		}
		self.states[current].text = Some(output.to_string());
	}

	/// Simulates the current transducer using the specified input.
	///
	/// This is a slower version of the transducer transformation at the
	/// current state. It runs without compiling the transducer, and is mostly
	/// useful for debugging.
	pub fn simulate<S: AsRef<str>>(&self, input: S) -> String {
		let (output, _) = self.run_machine(input.as_ref(), true);
		output
	}

	/// Compiles the [`Transducer`].
	pub fn compile(&self) -> Transducer {
		let mut program = Vec::new();
		let mut input = String::new();
		let mut state_map = HashMap::new();
		let start = self.compile_subtree(&mut program, 0, &None, 0, &mut input, &mut state_map);

		// translate all jumps to the actual operation offset
		for op in program.iter_mut() {
			if let Op::Jump { next } = op {
				*next = *state_map.get(&next).unwrap();
			}
		}

		//--------------------------------------------------------------------//
		// Optimization
		//--------------------------------------------------------------------//

		/// Applies a transformation to every transition target in the program.
		fn transform_target<F: Fn(usize) -> usize>(program: &mut Vec<Op>, transform: F) {
			for op in program.iter_mut() {
				match op {
					Op::Char { .. } => {}
					Op::Jump { .. } => {}

					Op::Push { next, .. } => {
						*next = transform(*next);
					}
					Op::Read { fail, next, char: _ } => {
						if let Action::Next(next) = next {
							*next = transform(*next);
						}
						if let Action::Next(fail) = fail {
							*fail = transform(*fail);
						}
					}
					Op::Test { table, fail } => {
						if let Action::Next(fail) = fail {
							*fail = transform(*fail);
						}
						for (_, next) in table.iter_mut() {
							if let Action::Next(next) = next {
								*next = transform(*next);
							}
						}
					}
				}
			}
		}

		/// Applies a transformation to every transition action in the program.
		///
		/// This only affect the actions in [`Op::Read`] and [`Op::Test`] which
		/// allow actions.
		fn transform_action<F: Fn(Action) -> Action>(program: &mut Vec<Op>, transform: F) {
			for op in program.iter_mut() {
				match op {
					Op::Char { .. } => {}
					Op::Jump { .. } => {}
					Op::Push { .. } => {}

					Op::Read { fail, next, char: _ } => {
						*next = transform(*next);
						*fail = transform(*fail);
					}
					Op::Test { table, fail } => {
						*fail = transform(*fail);
						for (_, next) in table.iter_mut() {
							*next = transform(*next);
						}
					}
				}
			}
		}

		//----| Remove jumps |------------------------------------------------//

		// This will replace all incondicional jumps with the direct target of
		// the jump.

		// if the index is a jump instruction, this will contain the target of
		// the jump at that index
		let mut jump_target: HashMap<usize, usize> = HashMap::new();
		for (index, op) in program.iter().enumerate() {
			if let Op::Jump { next } = op {
				jump_target.insert(index, *next);
			}
		}

		// takes a target offset and compute the new target after going through
		// any incondicional jumps
		let jump_target = move |mut next: usize| -> usize {
			// while the target is a jump, translate to the jump target
			while let Some(n) = jump_target.get(&next) {
				next = *n;
			}
			next
		};

		// translate all jump offsets in the program
		let start = jump_target(start);
		transform_target(&mut program, jump_target);

		//----| Replace single-output states |--------------------------------//

		// Find states that generate a single output character and move to the
		// start and replace with a direct output action.

		let end_target = program
			.iter()
			.enumerate()
			.filter_map(|(index, op)| {
				if let Op::Push { next, char } = op {
					if *next == start {
						return Some((index, *char));
					}
				}
				None
			})
			.collect::<HashMap<_, _>>();

		let end_target = move |action: Action| -> Action {
			if let Action::Next(next) = action {
				if let Some(char) = end_target.get(&next) {
					return Action::Char(*char);
				}
			}
			action
		};

		transform_action(&mut program, end_target);

		//----| Remove unused ops |-------------------------------------------//

		// ~ Flag used ops ~

		// breadth-first search starting at the initial state
		let mut used: HashSet<usize> = HashSet::new();
		let mut queue: VecDeque<usize> = VecDeque::new();
		queue.push_back(start);
		while let Some(index) = queue.pop_front() {
			if used.insert(index) {
				match &program[index] {
					Op::Char { .. } => {}
					Op::Jump { next } => {
						queue.push_back(*next);
					}
					Op::Push { next, .. } => {
						queue.push_back(*next);
					}
					Op::Read { fail, next, char: _ } => {
						if let Action::Next(next) = next {
							queue.push_back(*next);
						}
						if let Action::Next(fail) = fail {
							queue.push_back(*fail);
						}
					}
					Op::Test { table, fail } => {
						if let Action::Next(fail) = fail {
							queue.push_back(*fail);
						}
						for (_, next) in table.iter() {
							if let Action::Next(next) = next {
								queue.push_back(*next);
							}
						}
					}
				}
			}
		}

		// ~ Compute the new offset for each operation index ~

		// number of unused operations before a given index
		let mut unused_count: Vec<usize> = Vec::with_capacity(program.len());
		let mut unused = 0;
		for index in 0..program.len() {
			unused_count.push(unused);
			if !used.contains(&index) {
				unused += 1;
			}
		}

		// adjust the targets of each operation based on the to be removed
		// unused operations' offset
		let start = start - unused_count[start];
		for op in program.iter_mut() {
			match op {
				Op::Char { .. } => {}
				Op::Jump { next } => {
					*next -= unused_count[*next];
				}

				Op::Push { next, .. } => {
					*next -= unused_count[*next];
				}
				Op::Read { fail, next, char: _ } => {
					if let Action::Next(fail) = fail {
						*fail -= unused_count[*fail];
					}
					if let Action::Next(next) = next {
						*next -= unused_count[*next];
					}
				}
				Op::Test { table, fail } => {
					if let Action::Next(fail) = fail {
						*fail -= unused_count[*fail];
					}
					for (_, next) in table.iter_mut() {
						if let Action::Next(next) = next {
							*next -= unused_count[*next];
						}
					}
				}
			}
		}

		// ~ Remove unused ~

		program = program
			.into_iter()
			.enumerate()
			.filter(|(index, _)| if used.contains(index) { true } else { false })
			.map(|x| x.1)
			.collect();

		//--------------------------------------------------------------------//

		Transducer { start, program }
	}

	fn compile_subtree(
		&self,
		// output program
		out: &mut Vec<Op>,
		// the state index to generate
		state_index: usize,
		// last valid output state
		valid_output: &Option<String>,
		// consumed input by the last valid output state
		valid_input: usize,
		// entire input up to this state
		input: &mut String,
		// map of state indexes to operation
		state_map: &mut HashMap<usize, usize>,
	) -> usize {
		let state = &self.states[state_index];

		// if this state has an output defined, overwrite the last valid output
		let (valid_output, valid_input) = if state.text.is_some() {
			(&state.text, input.len())
		} else {
			(valid_output, valid_input)
		};

		// recursively generate any transition states and the corresponding
		// comparison operation, returning the index of the entry operation
		let index = match state.next.len() {
			0 => out.len(),
			1 => {
				// single transition case
				let (&char, &next) = state.next.iter().next().unwrap();
				input.push(char);
				let next = self.compile_subtree(out, next, valid_output, valid_input, input, state_map);
				input.pop();

				let index = out.len();
				let fail = index + 1;
				out.push(Op::Read {
					char,
					next: Action::Next(next),
					fail: Action::Next(fail),
				});
				index
			}
			_ => {
				// multiple transition case
				let mut table = state.next.iter().collect::<Vec<_>>();
				table.sort();
				let table = table
					.into_iter()
					.map(|(&char, &next)| {
						input.push(char);
						let next = self.compile_subtree(out, next, valid_output, valid_input, input, state_map);
						input.pop();
						(char, Action::Next(next))
					})
					.collect::<HashMap<_, _>>();

				let index = out.len();
				let fail = index + 1;
				out.push(Op::Test {
					table,
					fail: Action::Next(fail),
				});
				index
			}
		};

		state_map.insert(state_index, index);

		// generate the `fail` target of the above transitions, or just the
		// output for a output-only state

		let consumed_input = if let Some(output) = valid_output {
			// generate the valid output up to this state
			for char in output.chars() {
				let next = out.len() + 1;
				out.push(Op::Push { char, next });
			}
			// we will re-evaluate the unprocessed characters after the valid
			// output
			valid_input
		} else if let Some(char) = input.chars().next() {
			// if there is no valid output, but we have consumed some input,
			// emit a single input character and re-evaluate the rest
			let next = out.len() + 1;
			out.push(Op::Push { char, next });
			char.len_utf8()
		} else {
			// there is no valid output and we also did not consume any input
			// previously (basically, we failed to match on the first character)
			out.push(Op::Char);
			0
		};

		// takes the unconsumed input and simulate the machine running using
		// that as input from the start, so that we can generate that output
		// and move to that state
		let (output, state_index) = self.run_machine(&input[consumed_input..], false);

		for char in output.chars() {
			let next = out.len() + 1;
			out.push(Op::Push { char, next });
		}

		// generate the jump with the state index, since we may not have that
		// state compiled yet
		out.push(Op::Jump { next: state_index });

		index
	}

	/// Simulates the machine running for the given input and returns the output
	/// and final state for it.
	fn run_machine(&self, input: &str, complete: bool) -> (String, usize) {
		// machine output
		let mut output = String::new();

		// current machine state
		let mut current = 0;

		// pending input to process
		let mut input = input;

		// the last valid output state encountered as `(output, cursor)`
		let mut valid_output: Option<(&String, usize)> = None;

		let mut cursor = 0;
		while input.len() > 0 || current > 0 {
			let state = &self.states[current];
			if let Some(output) = &state.text {
				valid_output = Some((output, cursor));
			}

			// do we have a next character?
			let next = input[cursor..].chars().next();

			// Flushes the pending output, advances the input pointer, and
			// resets the machine state. This is called at a final state in
			// the machine.
			let mut push = || {
				// output either the last valid output or the first input
				// character, advancing input to the next unprocessed position
				if let Some((text, pos)) = valid_output.take() {
					output.push_str(text);
					input = &input[pos..];
				} else if let Some(char) = input.chars().next() {
					output.push(char);
					input = &input[char.len_utf8()..];
				}

				// reset the machine state
				cursor = 0;
				current = 0;
			};

			if let Some(char) = next {
				// if we have a valid transition just advance to the next state
				if let Some(&next) = state.next.get(&char) {
					cursor += char.len_utf8();
					current = next;
				} else {
					// otherwise, output the last valid state and reset
					push();
				}
			} else {
				// end of input
				if complete {
					// if we are simulating a complete input then we handle it
					// as an unmatched case and generate the last valid output
					push();
				} else {
					// if instead, we are not simulating to completion, we stop
					// here since future inputs may affect the output
					break;
				}
			}
		}

		(output, current)
	}
}

#[derive(Debug, Clone)]
struct BuilderState {
	/// Output text for this state, if this is a final state.
	text: Option<String>,

	/// Next states per input character.
	next: HashMap<char, usize>,
}

impl BuilderState {
	fn new() -> Self {
		BuilderState {
			text: None,
			next: Default::default(),
		}
	}
}

//----------------------------------------------------------------------------//
// Tests
//----------------------------------------------------------------------------//

// spell-checker: disable

#[cfg(test)]
mod tests {
	use super::Builder;

	#[test]
	fn builder_can_simulate_empty() {
		let builder = Builder::new();
		assert_eq!(builder.simulate(""), "");
		assert_eq!(builder.simulate("abc"), "abc");
	}

	#[test]
	fn builder_can_simulate_basic() {
		let mut builder = Builder::new();
		builder.add("a", "A");
		builder.add("b", "B");
		builder.add("c", "C");
		assert_eq!(builder.simulate(""), "");
		assert_eq!(builder.simulate("abc123abc"), "ABC123ABC");
	}

	#[test]
	fn builder_can_simulate_complex() {
		let mut builder = Builder::new();
		builder.add("1", "(one)");
		builder.add("10", "(ten)");
		builder.add("100", "(hundred)");
		builder.add("10000", "(ten thousand)");
		assert_eq!(
			builder.simulate("1/10/100/10000/100010"),
			"(one)/(ten)/(hundred)/(ten thousand)/(hundred)0(ten)"
		);
	}

	#[test]
	fn transducer_empty() {
		let t = Builder::new().compile();
		assert_eq!(t.parse_str(""), "");
		assert_eq!(t.parse_str("0"), "0");
		assert_eq!(t.parse_str("abc"), "abc");
	}

	#[test]
	fn transducer_basic() {
		let mut b = Builder::new();
		b.add("a", "A");
		b.add("b", "B");
		b.add("c", "C");

		let t = b.compile();

		assert_eq!(t.parse_str(""), "");
		assert_eq!(t.parse_str("!"), "!");
		assert_eq!(t.parse_str("a"), "A");
		assert_eq!(t.parse_str("b"), "B");
		assert_eq!(t.parse_str("c"), "C");
		assert_eq!(t.parse_str("abc"), "ABC");
		assert_eq!(t.parse_str("~abc"), "~ABC");
		assert_eq!(t.parse_str("abc~"), "ABC~");
		assert_eq!(t.parse_str("(abc)(aa)(bb)(cc)"), "(ABC)(AA)(BB)(CC)");
	}

	#[test]
	fn transducer_simple() {
		let mut b = Builder::new();
		b.add("a", "A");
		b.add("b", "B");
		b.add("ab", "C");

		assert_eq!(b.simulate("aabbabab123"), "ACBCC123");

		let t = b.compile();
		println!("{}", t);
		assert_eq!(t.parse_str("aabbabab123"), "ACBCC123");
	}

	#[test]
	fn transducer_end_of_input() {
		let mut b = Builder::new();
		b.add("aaax", "1");
		b.add("bbbx", "2");

		let t = b.compile();
		assert_eq!(t.parse_str("a"), "a");
		assert_eq!(t.parse_str("aa"), "aa");
		assert_eq!(t.parse_str("aaa"), "aaa");
		assert_eq!(t.parse_str("aaax"), "1");
		assert_eq!(t.parse_str("aaaxb"), "1b");
		assert_eq!(t.parse_str("aaaxbb"), "1bb");
		assert_eq!(t.parse_str("aaaxbbb"), "1bbb");
		assert_eq!(t.parse_str("aaaxbbbx"), "12");
	}

	#[test]
	fn transducer_empty_output() {
		let mut b = Builder::new();
		b.add("aaa", "");

		let t = b.compile();
		assert_eq!(t.parse_str("a"), "a");
		assert_eq!(t.parse_str("aa"), "aa");
		assert_eq!(t.parse_str("aaa"), "");
		assert_eq!(t.parse_str("aaaa"), "a");
		assert_eq!(t.parse_str("aaaaa"), "aa");
		assert_eq!(t.parse_str("aaaaaa"), "");

		assert_eq!(t.parse_str("(a)"), "(a)");
		assert_eq!(t.parse_str("(aa)"), "(aa)");
		assert_eq!(t.parse_str("(aaa)"), "()");

		assert_eq!(t.parse_str("(aaa)(a)"), "()(a)");
		assert_eq!(t.parse_str("(aaa)(aa)"), "()(aa)");
		assert_eq!(t.parse_str("(aaa)(aaa)"), "()()");

		assert_eq!(t.parse_str("(aaaa)"), "(a)");
		assert_eq!(t.parse_str("(aaaaa)"), "(aa)");
		assert_eq!(t.parse_str("(aaaaaa)"), "()");
	}

	#[test]
	fn transducer_tricky() {
		let mut b = Builder::new();
		b.add("a", "A");
		b.add("ab", "B");
		b.add("abab", "C");
		b.add("ababx", "X");
		b.add("aaaaaa", "Y");

		let t = b.compile();

		// non-matches
		assert_eq!(t.parse_str(""), "");
		assert_eq!(t.parse_str("b"), "b");

		// a-sequence
		assert_eq!(t.parse_str("a"), "A");
		assert_eq!(t.parse_str("aa"), "AA");
		assert_eq!(t.parse_str("aaa"), "AAA");
		assert_eq!(t.parse_str("aaaa"), "AAAA");
		assert_eq!(t.parse_str("aaaaa"), "AAAAA");
		assert_eq!(t.parse_str("aaaaaa"), "Y");
		assert_eq!(t.parse_str("aaaaaaa"), "YA");
		assert_eq!(t.parse_str("aaaaaaaaaaaa"), "YY");

		assert_eq!(t.parse_str("(a)"), "(A)");
		assert_eq!(t.parse_str("(aa)"), "(AA)");
		assert_eq!(t.parse_str("(aaa)"), "(AAA)");
		assert_eq!(t.parse_str("(aaaa)"), "(AAAA)");
		assert_eq!(t.parse_str("(aaaaa)"), "(AAAAA)");
		assert_eq!(t.parse_str("(aaaaaa)"), "(Y)");
		assert_eq!(t.parse_str("(aaaaaaa)"), "(YA)");
		assert_eq!(t.parse_str("(aaaaaaaaaaaa)"), "(YY)");

		// ab-sequences
		assert_eq!(t.parse_str("ab"), "B");
		assert_eq!(t.parse_str("aba"), "BA");
		assert_eq!(t.parse_str("abab"), "C");
		assert_eq!(t.parse_str("ababx"), "X");
		assert_eq!(t.parse_str("aababx"), "AX");

		assert_eq!(t.parse_str("(ab)"), "(B)");
		assert_eq!(t.parse_str("(aba)"), "(BA)");
		assert_eq!(t.parse_str("(abab)"), "(C)");
		assert_eq!(t.parse_str("(ababx)"), "(X)");
		assert_eq!(t.parse_str("(aababx)"), "(AX)");
	}
}
