use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::{spanned::Spanned, DeriveInput, FieldsNamed};

// derive(FromUserType) for the new API
pub fn from_user_type_derive(tokens_input: TokenStream) -> TokenStream {
    let item = syn::parse::<DeriveInput>(tokens_input).expect("No DeriveInput");
    let struct_fields = crate::parser::parse_named_fields(&item, "FromUserType");

    let struct_name = &item.ident;
    let (impl_generics, ty_generics, where_clause) = item.generics.split_for_impl();

    // TODO: Re-export those definitions in scylla?
    // On the other hand, this would prevent those macros being used
    // with scylla-cql alone/
    let generated = quote! {
        impl #impl_generics ::scylla_cql::
    }
}
