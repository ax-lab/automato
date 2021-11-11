use automato_macros::transducer;

#[test]
fn simple_kana() {
	transducer!(kana:
		"じ" => "ji",
		"じゃ" => "ja",
		"じょ" => "jo",
		"じゅ" => "ju",
		"あ" => "a",
		"い" => "i",
		"う" => "u",
		"え" => "e",
		"お" => "o",
		"か" => "ka",
		"き" => "ki",
		"く" => "ku",
		"け" => "ke",
		"こ" => "ko",
	);

	let out: String = kana::new("じゃあ!".chars()).collect();
	assert_eq!(out, "jaa!");
}
