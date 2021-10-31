use std::{
	cell::RefCell,
	marker::PhantomData,
	rc::Rc,
	sync::atomic::{AtomicUsize, Ordering},
};

use crate::CharRange;

//----------------------------------------------------------------------------//
// DFA
//----------------------------------------------------------------------------//

/// A simple Deterministic Finite Automaton. New instances are created
/// using [`Builder`].
#[derive(Debug)]
pub struct DFA {
	states: Vec<State>,
}

#[derive(Debug)]
struct State {
	valid: bool,
	next: Vec<(usize, CharRange)>,
}

impl DFA {
	/// Matches a string.
	pub fn matches_str<S: AsRef<str>>(&self, input: S) -> bool {
		self.matches(input.as_ref().chars())
	}

	/// Matches an iterator of characters..
	pub fn matches<T: IntoIterator<Item = char>>(&self, input: T) -> bool {
		let mut state_index = 0;
		for char in input {
			let state = &self.states[state_index];
			if let Some(&(next_index, _)) = state.next.iter().find(|(_, chars)| chars.contains(char)) {
				state_index = next_index;
			} else {
				return false;
			}
		}
		self.states[state_index].valid
	}
}

//----------------------------------------------------------------------------//
// DFA builder
//----------------------------------------------------------------------------//

static COUNTER: AtomicUsize = AtomicUsize::new(1);

/// Builder for a [`DFA`].
#[derive(Debug, Clone)]
pub struct Builder {
	info: Rc<RefCell<BuilderInfo>>,
}

impl Builder {
	/// Uses the given callback to configurate a [`Builder`] instance.
	///
	/// Returns a new [`DFA`] with the given settings.
	pub fn create<F: FnOnce(&Builder)>(config: F) -> DFA {
		let builder = Builder {
			info: Rc::new(RefCell::new(BuilderInfo {
				id: COUNTER.fetch_add(1, Ordering::Relaxed),
				states: vec![BuilderStateInfo {
					valid: false,
					next: Vec::new(),
				}],
			})),
		};
		config(&builder);
		builder.finish()
	}

	/// Returns the starting state for the [`DFA`] being built.
	pub fn start(&self) -> BuilderState {
		BuilderState {
			info: self.info.clone(),
			index: 0,
			_phantom: PhantomData,
		}
	}

	/// Builds and returns the [`DFA`] described by this builder.
	fn finish(self) -> DFA {
		let info = Rc::try_unwrap(self.info).unwrap().into_inner();
		DFA {
			states: info
				.states
				.into_iter()
				.map(|state| State {
					valid: state.valid,
					next: state.next,
				})
				.collect(),
		}
	}
}

/// Allows the configuration of a single state in the DFA.
#[derive(Debug, Clone)]
pub struct BuilderState<'a> {
	info: Rc<RefCell<BuilderInfo>>,
	index: usize,

	// we use this only to prevent using a `BuilderState` after the
	// parent `Builder` is used.
	_phantom: PhantomData<&'a Builder>,
}

#[derive(Debug, Clone)]
struct BuilderInfo {
	id: usize,
	states: Vec<BuilderStateInfo>,
}

#[derive(Debug, Clone)]
struct BuilderStateInfo {
	valid: bool,
	next: Vec<(usize, CharRange)>,
}

impl<'a> BuilderState<'a> {
	/// Creates a new next state for the current state with the [`CharRange`]
	/// as transition.
	///
	/// Returns the newly created state.
	pub fn next(&self, chars: CharRange) -> BuilderState {
		let new_index = {
			let mut info = self.info.borrow_mut();

			info.states.push(BuilderStateInfo {
				valid: false,
				next: Vec::new(),
			});

			let new_index = info.states.len() - 1;
			info.states[self.index].next.push((new_index, chars));
			new_index
		};

		BuilderState {
			info: self.info.clone(),
			index: new_index,
			_phantom: self._phantom,
		}
	}

	/// Links the current state to the another state with the [`CharRange`]
	/// as transition.
	///
	/// Returns `self`.
	pub fn link(self, other: &BuilderState, chars: CharRange) -> Self {
		let other_id = { other.info.borrow().id };
		let mut info = self.info.borrow_mut();
		if other_id != info.id {
			panic!("BuilderState.link: cannot link with the state of another Builder")
		}
		info.states[self.index].next.push((other.index, chars));
		drop(info);
		self
	}

	/// Set the current state as a valid final state.
	///
	/// Returns `self`.
	pub fn set_final(self) -> Self {
		let mut info = self.info.borrow_mut();
		info.states[self.index].valid = true;
		drop(info);
		self
	}
}

//----------------------------------------------------------------------------//
// Tests
//----------------------------------------------------------------------------//

#[cfg(test)]
mod tests {
	use super::Builder;

	#[test]
	fn empty_dfa() {
		let dfa = Builder::create(|_| {});
		assert!(!dfa.matches_str(""));
		assert!(!dfa.matches_str("x"));

		let dfa = Builder::create(|builder| {
			builder.start().set_final();
		});
		assert!(dfa.matches_str(""));
		assert!(!dfa.matches_str("x"));
	}

	#[test]
	fn basic_dfa() {
		let dfa = Builder::create(|builder| {
			let s = builder.start();
			let a = s.next('a'.into());
			let b = a.next('b'.into());
			let c = b.next('c'.into());
			c.set_final();
		});
		assert!(dfa.matches_str("abc"));
		assert!(!dfa.matches_str(""));
		assert!(!dfa.matches_str("a"));
		assert!(!dfa.matches_str("x"));
		assert!(!dfa.matches_str("ab"));
		assert!(!dfa.matches_str("abcd"));
	}

	#[test]
	fn simple_branch() {
		let dfa = Builder::create(|builder| {
			let s = builder.start();
			let a = s.next('a'.into());
			let f1 = a.next('1'.into());
			let f2 = a.next('2'.into());
			f1.set_final();
			f2.set_final();
		});
		assert!(dfa.matches_str("a1"));
		assert!(dfa.matches_str("a2"));
		assert!(!dfa.matches_str(""));
		assert!(!dfa.matches_str("a"));
		assert!(!dfa.matches_str("a3"));
		assert!(!dfa.matches_str("a1x"));
	}
}
