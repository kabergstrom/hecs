use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{DeriveInput, Result};

pub fn derive(input: DeriveInput) -> Result<TokenStream2> {
    let ident = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    // For generic types, the hash would need to include type parameters.
    // This is out of scope — generic component types are not supported yet.
    if !input.generics.params.is_empty() {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "derive(Component) does not yet support generic types",
        ));
    }

    Ok(quote! {
        impl #impl_generics ::hecs::Component for #ident #ty_generics #where_clause {
            const STABLE_TYPE_ID: ::hecs::StableTypeId = ::hecs::StableTypeId(
                ::hecs::StableTypeId::fnv1a(
                    concat!(module_path!(), "::", stringify!(#ident)).as_bytes()
                )
            );
            const TYPE_NAME: &'static str = concat!(module_path!(), "::", stringify!(#ident));
        }
    })
}
