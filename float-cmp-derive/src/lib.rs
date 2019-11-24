
extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro_derive(FloatCmp)]
pub fn derive_float_cmp(_item: TokenStream) -> TokenStream {
    "// FloatCmp derive is TBD".parse().unwrap()
}
