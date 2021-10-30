use crate::intersect;
use std::{
	collections::HashSet,
	ops::{Range, RangeInclusive},
};

/// Represents a range of characters. This is used in FSM transitions.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum CharRange {
	/// Empty character range.
	None,
	/// A single character.
	Single(char),
	/// Open-ended range of characters.
	Exclusive(char, char),
	/// Close-ended range of characters.
	Inclusive(char, char),
	/// Set of characters.
	Set(HashSet<char>),
}

impl Default for CharRange {
	fn default() -> Self {
		CharRange::None
	}
}

impl From<char> for CharRange {
	fn from(value: char) -> Self {
		CharRange::Single(value)
	}
}

impl From<&str> for CharRange {
	fn from(value: &str) -> Self {
		let set: HashSet<_> = value.chars().collect();
		CharRange::Set(set).simplify()
	}
}

impl From<Range<char>> for CharRange {
	fn from(value: Range<char>) -> Self {
		if value.start < value.end {
			CharRange::Exclusive(value.start, value.end).simplify()
		} else {
			CharRange::None
		}
	}
}

impl From<RangeInclusive<char>> for CharRange {
	fn from(value: RangeInclusive<char>) -> Self {
		let start = *value.start();
		let end = *value.end();
		CharRange::Inclusive(start, end).simplify()
	}
}

impl CharRange {
	/// Returns true if this range contains the given character.
	pub fn contains(&self, char: char) -> bool {
		match self {
			CharRange::None => false,
			&CharRange::Single(value) => value == char,
			&CharRange::Inclusive(start, end) => char >= start && char <= end,
			&CharRange::Exclusive(start, end) => char >= start && char < end,
			CharRange::Set(str) => str.contains(&char),
		}
	}

	/// Returns true if there is an intersection between the current range and
	/// the given `other` range.
	pub fn intersects(&self, other: &CharRange) -> bool {
		match self {
			CharRange::None => false,
			&CharRange::Single(char) => other.contains(char),
			&CharRange::Inclusive(start, end) => other.intersects_range(start, end, true),
			&CharRange::Exclusive(start, end) => other.intersects_range(start, end, false),
			CharRange::Set(str) => str.iter().any(|c| other.contains(*c)),
		}
	}

	/// Returns the intersection between this range and the given `other` range.
	pub fn intersection(&self, other: &CharRange) -> CharRange {
		let out = match self {
			CharRange::None => CharRange::None,
			&CharRange::Single(char) => {
				if other.contains(char) {
					CharRange::Single(char)
				} else {
					CharRange::None
				}
			}
			&CharRange::Inclusive(start, end) => other.get_range_intersection(start, end, true),
			&CharRange::Exclusive(start, end) => other.get_range_intersection(start, end, false),
			CharRange::Set(str) => other.get_set_intersection(&str),
		};
		out.simplify()
	}

	/// When possible, simplifies character ranges and sets.
	///
	/// This will return [`CharRange::Single`] and [`CharRange::None`] when
	/// possible.
	pub fn simplify(self) -> CharRange {
		match self {
			CharRange::Inclusive(start, end) => {
				if start == end {
					CharRange::Single(start)
				} else {
					CharRange::Inclusive(start, end)
				}
			}
			CharRange::Exclusive(start, end) => {
				if start == end {
					CharRange::None
				} else if (start as u32) + 1 == (end as u32) {
					CharRange::Single(start)
				} else {
					CharRange::Exclusive(start, end)
				}
			}
			CharRange::Set(set) => match set.len() {
				0 => CharRange::None,
				1 => CharRange::Single(set.into_iter().next().unwrap()),
				_ => CharRange::Set(set),
			},
			_ => self,
		}
	}

	//----[ Private helpers ]-------------------------------------------------//

	fn intersects_range(&self, start: char, end: char, inclusive: bool) -> bool {
		match self {
			CharRange::None => false,
			&CharRange::Single(a) => a >= start && (a < end || (inclusive && a <= end)),
			&CharRange::Inclusive(a, b) => intersect::check(&(start, end, inclusive), &(a, b, true)),
			&CharRange::Exclusive(a, b) => intersect::check(&(start, end, inclusive), &(a, b, false)),
			CharRange::Set(str) => str.iter().any(|&a| a >= start && (a < end || (inclusive && a <= end))),
		}
	}

	fn get_range_intersection(&self, start: char, end: char, inclusive: bool) -> CharRange {
		match self {
			CharRange::None => CharRange::None,
			&CharRange::Single(a) => {
				if a >= start && (a < end || (inclusive && a == end)) {
					CharRange::Single(a)
				} else {
					CharRange::None
				}
			}
			&CharRange::Inclusive(a, b) => CharRange::from_range(intersect::get((start, end, inclusive), (a, b, true))),
			&CharRange::Exclusive(a, b) => {
				CharRange::from_range(intersect::get((start, end, inclusive), (a, b, false)))
			}
			CharRange::Set(str) => CharRange::from_range(Some((start, end, inclusive))).get_set_intersection(&str),
		}
	}

	fn from_range(range: Option<(char, char, bool)>) -> CharRange {
		range
			.map(|(a, b, inclusive)| {
				if inclusive {
					CharRange::Inclusive(a, b)
				} else {
					CharRange::Exclusive(a, b)
				}
			})
			.unwrap_or(CharRange::None)
	}

	fn get_set_intersection(&self, str: &HashSet<char>) -> CharRange {
		let out: HashSet<char> = str.iter().cloned().filter(|c| self.contains(*c)).collect();
		if out.len() > 0 {
			CharRange::Set(out)
		} else {
			CharRange::None
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::CharRange;

	#[test]
	fn has_default() {
		let x: CharRange = Default::default();
		assert_eq!(x, CharRange::None);
	}

	#[test]
	fn can_convert_range_from_chars_and_strings() {
		let actual: CharRange = ('a'..'z').into();
		assert_eq!(actual, CharRange::Exclusive('a', 'z'));

		let actual: CharRange = ('a'..='z').into();
		assert_eq!(actual, CharRange::Inclusive('a', 'z'));

		let actual: CharRange = 'a'.into();
		assert_eq!(actual, CharRange::Single('a'));

		let actual: CharRange = "abc".into();
		assert_eq!(actual, CharRange::Set("abc".chars().collect()));

		let actual: CharRange = "".into();
		assert_eq!(actual, CharRange::None);

		let actual: CharRange = ('a'..='a').into();
		assert_eq!(actual, CharRange::Single('a'));

		let actual: CharRange = ('a'..'a').into();
		assert_eq!(actual, CharRange::None);

		let actual: CharRange = "a".into();
		assert_eq!(actual, CharRange::Single('a'));
	}

	#[test]
	fn range_contains() {
		let x = CharRange::None;
		assert!(!x.contains('0'));

		let x = CharRange::Single('1');
		assert!(x.contains('1'));
		assert!(!x.contains('0'));

		let x = CharRange::Inclusive('1', '3');
		assert!(x.contains('1'));
		assert!(x.contains('2'));
		assert!(x.contains('3'));
		assert!(!x.contains('4'));
		assert!(!x.contains('0'));

		let x = CharRange::Exclusive('1', '3');
		assert!(x.contains('1'));
		assert!(x.contains('2'));
		assert!(!x.contains('3'));
		assert!(!x.contains('4'));
		assert!(!x.contains('0'));

		let x = CharRange::Set("123".chars().collect());
		assert!(x.contains('1'));
		assert!(x.contains('2'));
		assert!(x.contains('3'));
		assert!(!x.contains('4'));
		assert!(!x.contains('0'));
	}

	#[test]
	fn range_simplify() {
		let x = CharRange::None;
		assert_eq!(x.simplify(), CharRange::None);

		let x = CharRange::Single('1');
		assert_eq!(x.simplify(), CharRange::Single('1'));

		let x = CharRange::Inclusive('1', '1');
		assert_eq!(x.simplify(), CharRange::Single('1'));

		let x = CharRange::Inclusive('1', '2');
		assert_eq!(x.simplify(), CharRange::Inclusive('1', '2'));

		let x = CharRange::Exclusive('1', '1');
		assert_eq!(x.simplify(), CharRange::None);

		let x = CharRange::Exclusive('1', '2');
		assert_eq!(x.simplify(), CharRange::Single('1'));

		let x = CharRange::Exclusive('1', '3');
		assert_eq!(x.simplify(), CharRange::Exclusive('1', '3'));

		let x = CharRange::Set("".chars().collect());
		assert_eq!(x.simplify(), CharRange::None);

		let x = CharRange::Set("1".chars().collect());
		assert_eq!(x.simplify(), CharRange::Single('1'));

		let x = CharRange::Set("12".chars().collect());
		assert_eq!(x.simplify(), CharRange::Set("12".chars().collect()));
	}

	#[test]
	fn range_intersects() {
		let x = CharRange::None;
		assert!(!x.intersects(&CharRange::default()));

		//----[ Single ]------------------------------------------------------//

		let x = CharRange::Single('1');

		assert!(x.intersects(&CharRange::Single('1')));

		assert!(x.intersects(&CharRange::Inclusive('0', '2')));
		assert!(x.intersects(&CharRange::Inclusive('1', '2')));
		assert!(x.intersects(&CharRange::Inclusive('0', '1')));

		assert!(x.intersects(&CharRange::Exclusive('1', '2')));
		assert!(x.intersects(&CharRange::Exclusive('0', '2')));

		assert!(x.intersects(&CharRange::Set("123".chars().collect())));

		// false
		assert!(!x.intersects(&CharRange::Single('0')));
		assert!(!x.intersects(&CharRange::Inclusive('0', '0')));
		assert!(!x.intersects(&CharRange::Exclusive('0', '1')));
		assert!(!x.intersects(&CharRange::Set("02".chars().collect())));

		//----[ Inclusive ]---------------------------------------------------//

		let x = CharRange::Inclusive('1', '3');

		assert!(x.intersects(&CharRange::Single('1')));
		assert!(x.intersects(&CharRange::Single('2')));
		assert!(x.intersects(&CharRange::Single('3')));

		assert!(x.intersects(&CharRange::Inclusive('1', '1')));
		assert!(x.intersects(&CharRange::Inclusive('2', '2')));
		assert!(x.intersects(&CharRange::Inclusive('3', '3')));
		assert!(x.intersects(&CharRange::Inclusive('0', '4')));

		assert!(x.intersects(&CharRange::Exclusive('1', '2')));
		assert!(x.intersects(&CharRange::Exclusive('2', '3')));
		assert!(x.intersects(&CharRange::Exclusive('3', '4')));
		assert!(x.intersects(&CharRange::Exclusive('0', '4')));

		assert!(x.intersects(&CharRange::Set("1".chars().collect())));
		assert!(x.intersects(&CharRange::Set("2".chars().collect())));
		assert!(x.intersects(&CharRange::Set("3".chars().collect())));

		// false
		assert!(!x.intersects(&CharRange::Single('0')));
		assert!(!x.intersects(&CharRange::Single('4')));
		assert!(!x.intersects(&CharRange::Inclusive('0', '0')));
		assert!(!x.intersects(&CharRange::Inclusive('4', '4')));
		assert!(!x.intersects(&CharRange::Exclusive('0', '1')));
		assert!(!x.intersects(&CharRange::Exclusive('1', '1')));
		assert!(!x.intersects(&CharRange::Exclusive('2', '2')));
		assert!(!x.intersects(&CharRange::Exclusive('3', '3')));
		assert!(!x.intersects(&CharRange::Exclusive('4', '5')));
		assert!(!x.intersects(&CharRange::Set("04".chars().collect())));

		//----[ Exclusive ]---------------------------------------------------//

		let x = CharRange::Exclusive('1', '4');

		assert!(x.intersects(&CharRange::Single('1')));
		assert!(x.intersects(&CharRange::Single('2')));
		assert!(x.intersects(&CharRange::Single('3')));

		assert!(x.intersects(&CharRange::Inclusive('1', '1')));
		assert!(x.intersects(&CharRange::Inclusive('2', '2')));
		assert!(x.intersects(&CharRange::Inclusive('3', '3')));
		assert!(x.intersects(&CharRange::Inclusive('0', '4')));

		assert!(x.intersects(&CharRange::Exclusive('1', '2')));
		assert!(x.intersects(&CharRange::Exclusive('2', '3')));
		assert!(x.intersects(&CharRange::Exclusive('3', '4')));
		assert!(x.intersects(&CharRange::Exclusive('0', '4')));

		assert!(x.intersects(&CharRange::Set("1".chars().collect())));
		assert!(x.intersects(&CharRange::Set("2".chars().collect())));
		assert!(x.intersects(&CharRange::Set("3".chars().collect())));

		// false
		assert!(!x.intersects(&CharRange::Single('0')));
		assert!(!x.intersects(&CharRange::Single('4')));
		assert!(!x.intersects(&CharRange::Inclusive('0', '0')));
		assert!(!x.intersects(&CharRange::Inclusive('4', '4')));
		assert!(!x.intersects(&CharRange::Exclusive('0', '1')));
		assert!(!x.intersects(&CharRange::Exclusive('1', '1')));
		assert!(!x.intersects(&CharRange::Exclusive('2', '2')));
		assert!(!x.intersects(&CharRange::Exclusive('3', '3')));
		assert!(!x.intersects(&CharRange::Exclusive('4', '5')));
		assert!(!x.intersects(&CharRange::Set("04".chars().collect())));

		//----[ Set ]---------------------------------------------------------//

		let x = CharRange::Set("123".chars().collect());

		assert!(x.intersects(&CharRange::Single('1')));
		assert!(x.intersects(&CharRange::Single('2')));
		assert!(x.intersects(&CharRange::Single('3')));

		assert!(x.intersects(&CharRange::Inclusive('1', '1')));
		assert!(x.intersects(&CharRange::Inclusive('2', '2')));
		assert!(x.intersects(&CharRange::Inclusive('3', '3')));
		assert!(x.intersects(&CharRange::Inclusive('0', '4')));

		assert!(x.intersects(&CharRange::Exclusive('1', '2')));
		assert!(x.intersects(&CharRange::Exclusive('2', '3')));
		assert!(x.intersects(&CharRange::Exclusive('3', '4')));
		assert!(x.intersects(&CharRange::Exclusive('0', '4')));

		assert!(x.intersects(&CharRange::Set("1".chars().collect())));
		assert!(x.intersects(&CharRange::Set("2".chars().collect())));
		assert!(x.intersects(&CharRange::Set("3".chars().collect())));

		// false
		assert!(!x.intersects(&CharRange::Single('0')));
		assert!(!x.intersects(&CharRange::Single('4')));
		assert!(!x.intersects(&CharRange::Inclusive('0', '0')));
		assert!(!x.intersects(&CharRange::Inclusive('4', '4')));
		assert!(!x.intersects(&CharRange::Exclusive('0', '1')));
		assert!(!x.intersects(&CharRange::Exclusive('1', '1')));
		assert!(!x.intersects(&CharRange::Exclusive('2', '2')));
		assert!(!x.intersects(&CharRange::Exclusive('3', '3')));
		assert!(!x.intersects(&CharRange::Exclusive('4', '5')));
		assert!(!x.intersects(&CharRange::Set("04".chars().collect())));
	}

	#[test]
	fn range_intersection() {
		let x = CharRange::None;
		assert_eq!(x.intersection(&CharRange::default()), CharRange::None);

		//----[ Single ]------------------------------------------------------//

		let x = CharRange::Single('1');

		assert_eq!(x.intersection(&CharRange::Single('1')), CharRange::Single('1'));

		assert_eq!(x.intersection(&CharRange::Inclusive('0', '2')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Inclusive('1', '2')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Inclusive('0', '1')), CharRange::Single('1'));

		assert_eq!(x.intersection(&CharRange::Exclusive('1', '2')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Exclusive('0', '2')), CharRange::Single('1'));

		assert_eq!(
			x.intersection(&CharRange::Set("123".chars().collect())),
			CharRange::Single('1')
		);

		// false
		assert_eq!(x.intersection(&CharRange::Single('0')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Inclusive('0', '0')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('0', '1')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Set("02".chars().collect())), CharRange::None);

		//----[ Inclusive ]---------------------------------------------------//

		let x = CharRange::Inclusive('1', '3');

		assert_eq!(x.intersection(&CharRange::Single('1')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Single('2')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Single('3')), CharRange::Single('3'));

		assert_eq!(x.intersection(&CharRange::Inclusive('1', '1')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Inclusive('2', '2')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Inclusive('3', '3')), CharRange::Single('3'));
		assert_eq!(
			x.intersection(&CharRange::Inclusive('0', '4')),
			CharRange::Inclusive('1', '3')
		);

		assert_eq!(x.intersection(&CharRange::Exclusive('1', '2')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Exclusive('2', '3')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Exclusive('3', '4')), CharRange::Single('3'));
		assert_eq!(
			x.intersection(&CharRange::Exclusive('0', '4')),
			CharRange::Inclusive('1', '3')
		);

		assert_eq!(
			x.intersection(&CharRange::Set("1".chars().collect())),
			CharRange::Single('1')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("2".chars().collect())),
			CharRange::Single('2')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("3".chars().collect())),
			CharRange::Single('3')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("1234".chars().collect())),
			CharRange::Set("123".chars().collect())
		);

		// false
		assert_eq!(x.intersection(&CharRange::Single('0')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Single('4')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Inclusive('0', '0')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Inclusive('4', '4')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('0', '1')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('1', '1')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('2', '2')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('3', '3')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('4', '5')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Set("04".chars().collect())), CharRange::None);

		//----[ Exclusive ]---------------------------------------------------//

		let x = CharRange::Exclusive('1', '4');

		assert_eq!(x.intersection(&CharRange::Single('1')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Single('2')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Single('3')), CharRange::Single('3'));

		assert_eq!(x.intersection(&CharRange::Inclusive('1', '1')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Inclusive('2', '2')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Inclusive('3', '3')), CharRange::Single('3'));
		assert_eq!(
			x.intersection(&CharRange::Inclusive('0', '4')),
			CharRange::Exclusive('1', '4')
		);

		assert_eq!(
			x.intersection(&CharRange::Inclusive('0', '3')),
			CharRange::Inclusive('1', '3')
		);

		assert_eq!(x.intersection(&CharRange::Exclusive('1', '2')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Exclusive('2', '3')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Exclusive('3', '4')), CharRange::Single('3'));
		assert_eq!(
			x.intersection(&CharRange::Exclusive('0', '4')),
			CharRange::Exclusive('1', '4')
		);

		assert_eq!(
			x.intersection(&CharRange::Inclusive('0', '3')),
			CharRange::Inclusive('1', '3')
		);

		assert_eq!(
			x.intersection(&CharRange::Set("1".chars().collect())),
			CharRange::Single('1')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("2".chars().collect())),
			CharRange::Single('2')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("3".chars().collect())),
			CharRange::Single('3')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("1234".chars().collect())),
			CharRange::Set("123".chars().collect())
		);

		// false
		assert_eq!(x.intersection(&CharRange::Single('0')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Single('4')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Inclusive('0', '0')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Inclusive('4', '4')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('0', '1')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('1', '1')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('2', '2')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('3', '3')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('4', '5')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Set("04".chars().collect())), CharRange::None);

		//----[ Set ]---------------------------------------------------------//

		let x = CharRange::Set("123".chars().collect());

		assert_eq!(x.intersection(&CharRange::Single('1')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Single('2')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Single('3')), CharRange::Single('3'));

		assert_eq!(x.intersection(&CharRange::Inclusive('1', '1')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Inclusive('2', '2')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Inclusive('3', '3')), CharRange::Single('3'));
		assert_eq!(
			x.intersection(&CharRange::Inclusive('0', '4')),
			CharRange::Set("123".chars().collect())
		);

		assert_eq!(x.intersection(&CharRange::Exclusive('1', '2')), CharRange::Single('1'));
		assert_eq!(x.intersection(&CharRange::Exclusive('2', '3')), CharRange::Single('2'));
		assert_eq!(x.intersection(&CharRange::Exclusive('3', '4')), CharRange::Single('3'));
		assert_eq!(
			x.intersection(&CharRange::Exclusive('0', '4')),
			CharRange::Set("123".chars().collect())
		);

		assert_eq!(
			x.intersection(&CharRange::Set("1".chars().collect())),
			CharRange::Single('1')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("2".chars().collect())),
			CharRange::Single('2')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("3".chars().collect())),
			CharRange::Single('3')
		);
		assert_eq!(
			x.intersection(&CharRange::Set("1234".chars().collect())),
			CharRange::Set("123".chars().collect())
		);

		// false
		assert_eq!(x.intersection(&CharRange::Single('0')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Single('4')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Inclusive('0', '0')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Inclusive('4', '4')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('0', '1')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('1', '1')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('2', '2')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('3', '3')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Exclusive('4', '5')), CharRange::None);
		assert_eq!(x.intersection(&CharRange::Set("04".chars().collect())), CharRange::None);
	}
}
