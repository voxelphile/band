use proc_macro::TokenStream;
use quote::quote;
use syn;

#[proc_macro_derive(Component)]
pub fn component_derive(input: TokenStream) -> TokenStream {
    let ast: syn::DeriveInput = syn::parse(input).unwrap();
    let name = &ast.ident;
    let gen = quote! {
        impl Data for #name {}
        impl Component for #name {}
    };
    gen.into()
}
