use automato::transducer::Builder;

fn main() {
	let mut b = Builder::new();
	b.add("in", "out");
	b.add("input", "output");
	b.add("a", "A");
	b.add("e", "E");
	b.add("i", "I");
	b.add("o", "O");
	b.add("u", "U");

	let transducer = b.compile();

	println!("\nCODE:\n\n");
	println!("{}", transducer.to_tokens());
}
