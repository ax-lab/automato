use automato::transducer::Builder;
use proc_macro::TokenStream;
use proc_macro2::Ident;
use quote::quote;
use syn::parse_macro_input;

#[proc_macro]
pub fn transducer_empty(id: TokenStream) -> TokenStream {
	let id = parse_macro_input!(id as Ident);

	let b = Builder::new();
	let tokens = b.compile().to_tokens();
	let tokens = quote! {
		mod #id {
			#tokens
		}
	};
	tokens.into()
}

#[proc_macro]
pub fn transducer_basic(id: TokenStream) -> TokenStream {
	let id = parse_macro_input!(id as Ident);
	let mut b = Builder::new();
	b.add("a", "A");
	b.add("b", "B");
	b.add("c", "C");

	let tokens = b.compile().to_tokens();
	let tokens = quote! {
		mod #id {
			#tokens
		}
	};
	tokens.into()
}

#[proc_macro]
pub fn transducer_simple(id: TokenStream) -> TokenStream {
	let id = parse_macro_input!(id as Ident);
	let mut b = Builder::new();
	b.add("a", "A");
	b.add("b", "B");
	b.add("ab", "C");

	let tokens = b.compile().to_tokens();
	let tokens = quote! {
		mod #id {
			#tokens
		}
	};
	tokens.into()
}

#[proc_macro]
pub fn transducer_end_of_input(id: TokenStream) -> TokenStream {
	let id = parse_macro_input!(id as Ident);
	let mut b = Builder::new();

	// spell-checker: ignore aaax bbbx
	b.add("aaax", "1");
	b.add("bbbx", "2");

	let tokens = b.compile().to_tokens();
	let tokens = quote! {
		mod #id {
			#tokens
		}
	};
	tokens.into()
}

#[proc_macro]
pub fn transducer_empty_output(id: TokenStream) -> TokenStream {
	let id = parse_macro_input!(id as Ident);
	let mut b = Builder::new();
	b.add("aaa", "");

	let tokens = b.compile().to_tokens();
	let tokens = quote! {
		mod #id {
			#tokens
		}
	};
	tokens.into()
}

#[proc_macro]
pub fn transducer_tricky(id: TokenStream) -> TokenStream {
	let id = parse_macro_input!(id as Ident);
	let mut b = Builder::new();

	// spell-checker: ignore ababx
	b.add("a", "A");
	b.add("ab", "B");
	b.add("abab", "C");
	b.add("ababx", "X");
	b.add("aaaaaa", "Y");

	let tokens = b.compile().to_tokens();
	let tokens = quote! {
		mod #id {
			#tokens
		}
	};
	tokens.into()
}
