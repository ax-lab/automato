/// Check if two intervals intersect. Intervals are given by a tuple with
/// the values `(start, end, inclusive)`.
pub fn check<T: PartialOrd>(a: &(T, T, bool), b: &(T, T, bool)) -> bool {
	// special check for empty ranges
	if (!a.2 && a.0 == a.1) || (!b.2 && b.0 == b.1) {
		return false;
	}

	/*
		To check for range intersection, it is easier to start from the two
		non-intersecting cases (assuming inclusive ranges):

		> A: a.0 > b.1
		> B: a.1 < b.0

		We want `!(A || B)`, which is equal to `!A && !B`, so:

		> a.0 <= b.1 && a.1 >= b.0

		The above is for inclusive ranges (i.e. `a.2` and `b.2`). For exclusive
		ranges, we also need `b.0 != a.1` and/or `a.0 != b.1`, so:

		> a.0 <= b.1 && (b.2 || a.0 != b.1) && a.1 >= b.0 && (a.2 || b.0 != a.1)

		Meaning, either a given range is inclusive, or that range end is not
		equal to the other range beginning.

		Note that the same result can be get by considering the range openness
		in the starting non-intersecting conditions.

		> A: a.0 > b.1 || (!b.2 && a.0 == b.1)
		> B: a.1 < b.0 || (!a.2 && b.0 == a.1)

		Given `!(X || (!Y && Z))` is equivalent to `!X && (Y || !Z)`:

		> !A = a.0 <= b.1 && (b.2 || a.0 != b.1)
		> !B = a.1 >= b.0 && (a.2 || b.0 != a.1)
	*/

	a.0 <= b.1 && (b.2 || a.0 != b.1) && a.1 >= b.0 && (a.2 || b.0 != a.1)
}

/// Returns the intersection of the given intervals, if any. Intervals are
/// given by a `(start, end, inclusive)` tuple.
pub fn get<T: PartialOrd>(a: (T, T, bool), b: (T, T, bool)) -> Option<(T, T, bool)> {
	if check(&a, &b) {
		let start = if a.0 > b.0 { a.0 } else { b.0 };
		if a.1 == b.1 {
			Some((start, a.1, a.2 && b.2))
		} else if a.1 < b.1 {
			Some((start, a.1, a.2))
		} else {
			Some((start, b.1, b.2))
		}
	} else {
		None
	}
}

#[cfg(test)]
mod tests {
	use std::fmt::Debug;

	use crate::intersect::check;
	use crate::intersect::get;

	#[test]
	fn check_works() {
		//----[ non-intersection ]--------------------------------------------//

		no((1, 3, true), (4, 6, true));
		no((1, 3, true), (4, 6, false));
		no((1, 3, false), (4, 6, true));
		no((1, 3, false), (4, 6, false));

		// corner cases
		no((1, 3, false), (3, 6, true));
		no((1, 3, false), (3, 6, false));

		no((1, 3, true), (2, 2, false));

		//----[ intersection ]------------------------------------------------//

		yes((2, 5, false), (3, 6, false));
		yes((2, 5, false), (1, 6, false));
		yes((2, 5, false), (3, 4, false));
		yes((2, 5, false), (1, 3, false));

		yes((2, 5, false), (3, 6, true));
		yes((2, 5, false), (1, 6, true));
		yes((2, 5, false), (3, 4, true));
		yes((2, 5, false), (1, 3, true));

		yes((2, 5, true), (3, 6, false));
		yes((2, 5, true), (1, 6, false));
		yes((2, 5, true), (3, 4, false));
		yes((2, 5, true), (1, 3, false));

		yes((2, 5, true), (3, 6, true));
		yes((2, 5, true), (1, 6, true));
		yes((2, 5, true), (3, 4, true));
		yes((2, 5, true), (1, 3, true));

		// corner cases
		yes((1, 3, true), (3, 6, true));
		yes((1, 3, true), (3, 6, false));
		yes((1, 3, true), (1, 3, true));
		yes((1, 3, true), (1, 3, false));
		yes((1, 3, false), (1, 3, false));
		yes((1, 3, false), (1, 3, true));

		//--------------------------------------------------------------------//

		fn yes<T: PartialOrd + Debug + Copy>(a: (T, T, bool), b: (T, T, bool)) {
			assert!(check(&a, &b), "{:?} and {:?} should intersect", a, b);
			assert!(check(&b, &a), "{:?} and {:?} should intersect", a, b);
		}

		fn no<T: PartialOrd + Debug + Copy>(a: (T, T, bool), b: (T, T, bool)) {
			assert!(!check(&a, &b), "{:?} and {:?} should not intersect", a, b);
			assert!(!check(&b, &a), "{:?} and {:?} should not intersect", a, b);
		}
	}

	#[test]
	fn get_works() {
		// non-intersection
		check((1, 3, false), (3, 6, true), None);

		// simple intersection
		check((1, 4, false), (2, 6, true), Some((2, 4, false)));
		check((1, 4, true), (2, 6, true), Some((2, 4, true)));

		// limit cases
		check((1, 3, true), (3, 6, true), Some((3, 3, true)));
		check((1, 3, true), (2, 3, true), Some((2, 3, true)));
		check((1, 3, true), (1, 2, true), Some((1, 2, true)));
		check((1, 3, true), (1, 2, false), Some((1, 2, false)));
		check((1, 3, false), (2, 3, true), Some((2, 3, false)));
		check((1, 3, true), (2, 3, false), Some((2, 3, false)));

		// openness handling
		check((1, 3, true), (1, 3, true), Some((1, 3, true)));
		check((1, 3, true), (1, 3, false), Some((1, 3, false)));
		check((1, 3, false), (1, 3, false), Some((1, 3, false)));

		fn check(a: (i32, i32, bool), b: (i32, i32, bool), expected: Option<(i32, i32, bool)>) {
			let actual = get(a, b);
			assert_eq!(actual, expected);

			let actual = get(b, a);
			assert_eq!(actual, expected);
		}
	}
}
