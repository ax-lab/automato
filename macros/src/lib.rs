use automato::transducer::{Builder, Transducer};
use proc_macro::TokenStream;
use proc_macro2::Ident;
use quote::quote;
use syn::{parse::Parse, parse_macro_input, LitStr, Token};

/// Generate a transducer as compiled code.
///
/// ## Example
///
/// ```
/// # extern crate automato_macros;
/// # use automato_macros::transducer;
/// transducer!(some_name:
///     "a" => "A",
///     "b" => "B",
///     "c" => "C",
/// );
/// let out = some_name::new("abc!".chars()).collect::<String>();
/// assert_eq!(out, "ABC!");
/// ```
#[proc_macro]
pub fn transducer(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input as ParsedTransducer);

	let tokens = input.compile().to_tokens();
	let name = input.name;
	let tokens = quote! {
		mod #name {
			#tokens
		}
	};
	tokens.into()
}

struct ParsedTransducer {
	pub name: Ident,
	pairs: Vec<InOut>,
}

impl ParsedTransducer {
	pub fn compile(&self) -> Transducer {
		let mut b = Builder::new();
		for InOut(src, dst) in self.pairs.iter() {
			b.add(src, dst);
		}
		b.compile()
	}
}

impl Parse for ParsedTransducer {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let name = input.call(Ident::parse)?;
		input.parse::<Token![:]>()?;

		let pairs = input.parse_terminated::<_, Token![,]>(InOut::parse)?;

		let out = ParsedTransducer {
			name,
			pairs: pairs.into_iter().collect(),
		};
		Ok(out)
	}
}

struct InOut(String, String);

impl Parse for InOut {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let src = input.parse::<LitStr>()?;
		input.parse::<Token![=>]>()?;
		let dst = input.parse::<LitStr>()?;
		let out = InOut(src.value(), dst.value());
		Ok(out)
	}
}
