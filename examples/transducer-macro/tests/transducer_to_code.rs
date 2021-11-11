use automato_macros::transducer;
use transducer_macro::{
	transducer_basic, transducer_empty, transducer_empty_output, transducer_simple, transducer_tricky,
};

#[test]
fn transducer_empty() {
	transducer_empty!(t);

	let out: String = t::new("".chars()).collect();
	assert_eq!(out, "");

	let out: String = t::new("0".chars()).collect();
	assert_eq!(out, "0");

	let out: String = t::new("abc".chars()).collect();
	assert_eq!(out, "abc");
}

#[test]
fn transducer_basic() {
	transducer_basic!(t);

	let out: String = t::new("".chars()).collect();
	assert_eq!(out, "");
	let out: String = t::new("!".chars()).collect();
	assert_eq!(out, "!");
	let out: String = t::new("a".chars()).collect();
	assert_eq!(out, "A");
	let out: String = t::new("b".chars()).collect();
	assert_eq!(out, "B");
	let out: String = t::new("c".chars()).collect();
	assert_eq!(out, "C");
	let out: String = t::new("abc".chars()).collect();
	assert_eq!(out, "ABC");
	let out: String = t::new("~abc".chars()).collect();
	assert_eq!(out, "~ABC");
	let out: String = t::new("abc~".chars()).collect();
	assert_eq!(out, "ABC~");
	let out: String = t::new("(abc)(aa)(bb)(cc)".chars()).collect();
	assert_eq!(out, "(ABC)(AA)(BB)(CC)");
}

#[test]
fn transducer_simple() {
	transducer_simple!(t);

	let out: String = t::new("aabbabab123".chars()).collect();
	assert_eq!(out, "ACBCC123");
}

#[test]
fn transducer_empty_output() {
	transducer_empty_output!(t);

	let out: String = t::new("a".chars()).collect();
	assert_eq!(out, "a");
	let out: String = t::new("aa".chars()).collect();
	assert_eq!(out, "aa");
	let out: String = t::new("aaa".chars()).collect();
	assert_eq!(out, "");
	let out: String = t::new("aaaa".chars()).collect();
	assert_eq!(out, "a");
	let out: String = t::new("aaaaa".chars()).collect();
	assert_eq!(out, "aa");
	let out: String = t::new("aaaaaa".chars()).collect();
	assert_eq!(out, "");

	let out: String = t::new("(a)".chars()).collect();
	assert_eq!(out, "(a)");
	let out: String = t::new("(aa)".chars()).collect();
	assert_eq!(out, "(aa)");
	let out: String = t::new("(aaa)".chars()).collect();
	assert_eq!(out, "()");

	let out: String = t::new("(aaa)(a)".chars()).collect();
	assert_eq!(out, "()(a)");
	let out: String = t::new("(aaa)(aa)".chars()).collect();
	assert_eq!(out, "()(aa)");
	let out: String = t::new("(aaa)(aaa)".chars()).collect();
	assert_eq!(out, "()()");

	let out: String = t::new("(aaaa)".chars()).collect();
	assert_eq!(out, "(a)");
	let out: String = t::new("(aaaaa)".chars()).collect();
	assert_eq!(out, "(aa)");
	let out: String = t::new("(aaaaaa)".chars()).collect();
	assert_eq!(out, "()");
}

#[test]
fn transducer_tricky() {
	transducer_tricky!(t);

	// non-matches
	let out: String = t::new("".chars()).collect();
	assert_eq!(out, "");
	let out: String = t::new("b".chars()).collect();
	assert_eq!(out, "b");

	// a-sequence
	let out: String = t::new("a".chars()).collect();
	assert_eq!(out, "A");
	let out: String = t::new("aa".chars()).collect();
	assert_eq!(out, "AA");
	let out: String = t::new("aaa".chars()).collect();
	assert_eq!(out, "AAA");
	let out: String = t::new("aaaa".chars()).collect();
	assert_eq!(out, "AAAA");
	let out: String = t::new("aaaaa".chars()).collect();
	assert_eq!(out, "AAAAA");
	let out: String = t::new("aaaaaa".chars()).collect();
	assert_eq!(out, "Y");
	let out: String = t::new("aaaaaaa".chars()).collect();
	assert_eq!(out, "YA");
	let out: String = t::new("aaaaaaaaaaaa".chars()).collect();
	assert_eq!(out, "YY");

	let out: String = t::new("(a)".chars()).collect();
	assert_eq!(out, "(A)");
	let out: String = t::new("(aa)".chars()).collect();
	assert_eq!(out, "(AA)");
	let out: String = t::new("(aaa)".chars()).collect();
	assert_eq!(out, "(AAA)");
	let out: String = t::new("(aaaa)".chars()).collect();
	assert_eq!(out, "(AAAA)");
	let out: String = t::new("(aaaaa)".chars()).collect();
	assert_eq!(out, "(AAAAA)");
	let out: String = t::new("(aaaaaa)".chars()).collect();
	assert_eq!(out, "(Y)");
	let out: String = t::new("(aaaaaaa)".chars()).collect();
	assert_eq!(out, "(YA)");
	let out: String = t::new("(aaaaaaaaaaaa)".chars()).collect();
	assert_eq!(out, "(YY)");

	// ab-sequences
	// spell-checker: ignore ababx aababx
	let out: String = t::new("ab".chars()).collect();
	assert_eq!(out, "B");
	let out: String = t::new("aba".chars()).collect();
	assert_eq!(out, "BA");
	let out: String = t::new("abab".chars()).collect();
	assert_eq!(out, "C");
	let out: String = t::new("ababx".chars()).collect();
	assert_eq!(out, "X");
	let out: String = t::new("aababx".chars()).collect();
	assert_eq!(out, "AX");

	let out: String = t::new("(ab)".chars()).collect();
	assert_eq!(out, "(B)");
	let out: String = t::new("(aba)".chars()).collect();
	assert_eq!(out, "(BA)");
	let out: String = t::new("(abab)".chars()).collect();
	assert_eq!(out, "(C)");
	let out: String = t::new("(ababx)".chars()).collect();
	assert_eq!(out, "(X)");
	let out: String = t::new("(aababx)".chars()).collect();
	assert_eq!(out, "(AX)");
}

#[test]
fn with_macro() {
	transducer!(basic:
		"a" => "A",
		"b" => "B",
		"c" => "C",
	);

	let out: String = basic::new("abc!".chars()).collect();
	assert_eq!(out, "ABC!");
}
