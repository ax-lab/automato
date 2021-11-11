use automato_macros::transducer;

#[test]
fn simple_macro() {
	transducer!(basic:
		"a" => "A",
		"b" => "B",
		"c" => "C",
	);

	let out: String = basic::new("abc!".chars()).collect();
	assert_eq!(out, "ABC!");
}
