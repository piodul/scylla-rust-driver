use darling::{FromAttributes, FromField};
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{ext::IdentExt, parse_quote};

use super::{DeserializeCommonFieldAttrs, DeserializeCommonStructAttrs};

#[derive(FromAttributes)]
#[darling(attributes(scylla))]
struct StructAttrs {
    #[darling(rename = "crate")]
    crate_path: Option<syn::Path>,

    // If true, then the type checking code will require the order of the fields
    // to be the same in both the Rust struct and the UDT. This allows the
    // deserialization to be slightly faster because looking struct fields up
    // by name can be avoided, though it is less convenient.
    #[darling(default)]
    enforce_order: bool,
}

impl DeserializeCommonStructAttrs for StructAttrs {
    fn crate_path(&self) -> syn::Path {
        match &self.crate_path {
            Some(path) => parse_quote!(#path::_macro_internal),
            None => parse_quote!(scylla::_macro_internal),
        }
    }
}

#[derive(FromField)]
#[darling(attributes(scylla))]
struct Field {
    // If true, then the field is not parsed at all, but it is initialized
    // with Default::default() instead. All other attributes are ignored.
    #[darling(default)]
    skip: bool,

    // If true, then - if this field is missing from the UDT fields - it will
    // be initialized to Default::default().
    // Not supported in enforce_order mode.
    #[darling(default)]
    default_when_missing: bool,

    // If set, then deserializes from the UDT field with this particular name
    // instead of the Rust field name.
    #[darling(default)]
    rename: Option<String>,

    ident: Option<syn::Ident>,
    ty: syn::Type,
}

impl DeserializeCommonFieldAttrs for Field {
    fn needs_default(&self) -> bool {
        self.skip || self.default_when_missing
    }

    fn deserialize_target(&self) -> syn::Type {
        self.ty.clone()
    }
}

// derive(DeserializeUserType) for the new API
pub fn deserialize_user_type_derive(
    tokens_input: TokenStream,
) -> Result<syn::ItemImpl, syn::Error> {
    let input = syn::parse(tokens_input)?;

    let implemented_trait: syn::Path = parse_quote!(types::deserialize::value::DeserializeCql);
    let constraining_trait = implemented_trait.clone();
    let s = StructDesc::new(&input, "DeserializeCql", constraining_trait)?;

    let items = vec![
        s.generate_type_check_method().into(),
        s.generate_deserialize_method().into(),
    ];

    Ok(s.generate_impl(implemented_trait, items))
}

impl Field {
    // Returns whether this field is mandatory for deserialization.
    fn is_required(&self) -> bool {
        !self.skip && !self.default_when_missing
    }

    // A Rust literal representing the name of this field
    fn cql_name_literal(&self) -> syn::LitStr {
        let field_name = match self.rename.as_ref() {
            Some(rename) => rename.to_owned(),
            None => self.ident.as_ref().unwrap().unraw().to_string(),
        };
        syn::LitStr::new(&field_name, Span::call_site())
    }
}

type StructDesc = super::StructDescForDeserialize<StructAttrs, Field>;

impl StructDesc {
    // Generates an expression which extracts the UDT fields or returns an error
    fn generate_extract_fields_from_type(&self, typ_expr: syn::Expr) -> syn::Expr {
        let crate_path = &self.struct_attrs().crate_path();
        parse_quote!(
            match #typ_expr {
                #crate_path::frame::response::result::ColumnType::UserDefinedType { field_types, .. } => field_types,
                _ => return ::std::result::Result::Err(
                    #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                        "Wrong type, expected an UDT".to_string(),
                    ),
                ),
            }
        )
    }

    fn generate_type_check_method(&self) -> syn::ImplItemMethod {
        if self.attrs.enforce_order {
            TypeCheckAssumeOrderGenerator(self).generate()
        } else {
            TypeCheckUnorderedGenerator(self).generate()
        }
    }

    fn generate_deserialize_method(&self) -> syn::ImplItemMethod {
        if self.attrs.enforce_order {
            DeserializeAssumeOrderGenerator(self).generate()
        } else {
            DeserializeUnorderedGenerator(self).generate()
        }
    }
}

struct TypeCheckAssumeOrderGenerator<'sd>(&'sd StructDesc);

impl<'sd> TypeCheckAssumeOrderGenerator<'sd> {
    // Generates the type_check method for when ensure_order == true.
    fn generate(&self) -> syn::ImplItemMethod {
        // The generated method will:
        // - Check that every required field appears on the list in the same order as struct fields
        // - Every type on the list is correct

        let crate_path = self.0.struct_attrs().crate_path();
        let fields = self.0.fields();
        let constraint_lifetime = self.0.constraint_lifetime();
        let extract_fields_expr = self.0.generate_extract_fields_from_type(parse_quote!(typ));
        let field_names = fields
            .iter()
            .filter(|f| !f.skip)
            .map(|f| f.cql_name_literal());
        let field_deserializers = fields
            .iter()
            .filter(|f| !f.skip)
            .map(|f| f.deserialize_target());
        let required_field_count = fields.iter().filter(|f| f.is_required()).count();
        let field_count_lit =
            syn::LitInt::new(&required_field_count.to_string(), Span::call_site());
        let numbers = 0usize..;

        parse_quote!(
            fn type_check(
                typ: &#crate_path::frame::response::result::ColumnType,
            ) -> ::std::result::Result<(), #crate_path::frame::frame_errors::ParseError> {
                // Extract information about the field types from the UDT
                // type definition.
                let fields = #extract_fields_expr;

                // Verify that the field count is correct
                if fields.len() != #field_count_lit {
                    return ::std::result::Result::Err(
                        #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                            ::std::format!(
                                "Wrong number of fields in a UDT, expected {} but got {}",
                                #field_count_lit,
                                fields.len(),
                            )
                        )
                    )
                }

                #(
                    let (name, typ) = &fields[#numbers];

                    // Verify the name
                    if name != #field_names {
                        return ::std::result::Result::Err(
                            #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                                ::std::format!(
                                    "Field #{} has wrong name, expected {} but got {}",
                                    #numbers,
                                    name,
                                    #field_names
                                )
                            )
                        )
                    }

                    // Verify the type
                    // TODO: Provide better context about which field this error is about
                    <#field_deserializers as #crate_path::types::deserialize::value::DeserializeCql<#constraint_lifetime>>::type_check(typ)?;
                )*

                // All is good!
                Ok(())
            }
        )
    }
}

struct DeserializeAssumeOrderGenerator<'sd>(&'sd StructDesc);

impl<'sd> DeserializeAssumeOrderGenerator<'sd> {
    fn generate_finalize_field(&self, field: &Field) -> syn::Expr {
        if field.skip {
            // Skipped fields are initialized with Default::default()
            return parse_quote!(::std::default::Default::default());
        }

        let crate_path = self.0.struct_attrs().crate_path();
        let cql_name_literal = field.cql_name_literal();
        let deserializer = field.deserialize_target();
        let constraint_lifetime = self.0.constraint_lifetime();
        parse_quote!(
            {
                let res = iter.next().ok_or_else(|| {
                    #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                        ::std::format!("Missing field: {}", #cql_name_literal)
                    )
                })?;
                let ((_, typ), value) = res?;
                // The value can be either
                // - None - missing from the serialized representation
                // - Some(None) - present in the serialized representation but null
                // For now, we treat both cases as "null".
                let value = value.flatten();
                <#deserializer as #crate_path::types::deserialize::value::DeserializeCql<#constraint_lifetime>>::deserialize(typ, value)?
            }
        )
    }

    fn generate(&self) -> syn::ImplItemMethod {
        // We can assume that type_check was called.

        let crate_path = self.0.struct_attrs().crate_path();
        let constraint_lifetime = self.0.constraint_lifetime();
        let fields = self.0.fields();

        let field_idents = fields.iter().map(|f| f.ident.as_ref().unwrap());
        let field_finalizers = fields.iter().map(|f| self.generate_finalize_field(f));

        #[allow(unused_mut)]
        let mut iterator_type =
            quote!(#crate_path::types::deserialize::value::UdtIterator<#constraint_lifetime>);

        parse_quote! {
            fn deserialize(
                typ: &#constraint_lifetime #crate_path::frame::response::result::ColumnType,
                v: ::std::option::Option<#crate_path::types::deserialize::FrameSlice<#constraint_lifetime>>,
            ) -> ::std::result::Result<Self, #crate_path::frame::frame_errors::ParseError> {
                // Create an iterator over the fields of the UDT.
                let mut iter = <#iterator_type as #crate_path::types::deserialize::value::DeserializeCql<#constraint_lifetime>>::deserialize(typ, v)?;

                Ok(Self {
                    #(#field_idents: #field_finalizers,)*
                })
            }
        }
    }
}

struct TypeCheckUnorderedGenerator<'sd>(&'sd StructDesc);

impl<'sd> TypeCheckUnorderedGenerator<'sd> {
    // An identifier for a bool variable that represents whether given
    // field was already visited during type check
    fn visited_flag_variable(field: &Field) -> syn::Ident {
        quote::format_ident!("visited_{}", field.ident.as_ref().unwrap().unraw())
    }

    // Generates a declaration of a "visited" flag for the purpose of type check.
    // We generate it even if the flag is not required in order to protect
    // from fields appearing more than once
    fn generate_visited_flag_decl(field: &Field) -> Option<syn::Stmt> {
        if field.skip {
            return None;
        }

        let visited_flag = Self::visited_flag_variable(field);
        Some(parse_quote!(let mut #visited_flag = false;))
    }

    // Generates code that, given variable `typ`, type-checks given field
    fn generate_type_check(&self, field: &Field) -> Option<syn::Block> {
        if field.skip {
            return None;
        }

        let crate_path = self.0.struct_attrs().crate_path();
        let constraint_lifetime = self.0.constraint_lifetime();
        let visited_flag = Self::visited_flag_variable(field);
        let typ = field.deserialize_target();
        let cql_name_literal = field.cql_name_literal();
        let decrement_if_required = if field.is_required() {
            quote!(remaining_required_fields -= 1;)
        } else {
            quote!()
        };
        Some(parse_quote!(
            {
                if !#visited_flag {
                    <#typ as #crate_path::types::deserialize::value::DeserializeCql<#constraint_lifetime>>::type_check(typ)?;
                    #visited_flag = true;
                    #decrement_if_required
                } else {
                    return ::std::result::Result::Err(
                        #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                            ::std::format!("Field {} occurs more than once in serialized data", #cql_name_literal),
                        ),
                    )
                }
            }
        ))
    }

    // Generates code that appends the flag name if it is missing.
    // The generated code is used to construct a nice error message.
    fn generate_append_name(field: &Field) -> Option<syn::Block> {
        if field.is_required() {
            let visited_flag = Self::visited_flag_variable(field);
            let cql_name_literal = field.cql_name_literal();
            Some(parse_quote!(
                {
                    if !#visited_flag {
                        missing_fields.push(#cql_name_literal);
                    }
                }
            ))
        } else {
            None
        }
    }

    // Generates the type_check method for when ensure_order == false.
    fn generate(&self) -> syn::ImplItemMethod {
        // The generated method will:
        // - Check that every required field appears on the list exactly once, in any order
        // - Every type on the list is correct

        let crate_path = &self.0.struct_attrs().crate_path();
        let fields = self.0.fields();
        let visited_field_declarations = fields.iter().flat_map(Self::generate_visited_flag_decl);
        let type_check_blocks = fields.iter().flat_map(|f| self.generate_type_check(f));
        let append_name_blocks = fields.iter().flat_map(Self::generate_append_name);
        let field_names = fields
            .iter()
            .filter(|f| !f.skip)
            .map(|f| f.cql_name_literal());
        let required_field_count = fields.iter().filter(|f| f.is_required()).count();
        let field_count_lit =
            syn::LitInt::new(&required_field_count.to_string(), Span::call_site());
        let extract_fields_expr = self.0.generate_extract_fields_from_type(parse_quote!(typ));

        parse_quote! {
            fn type_check(
                typ: &#crate_path::frame::response::result::ColumnType,
            ) -> ::std::result::Result<(), #crate_path::frame::frame_errors::ParseError> {
                // Extract information about the field types from the UDT
                // type definition.
                let fields = #extract_fields_expr;

                // Counts down how many required fields are remaining
                let mut remaining_required_fields: ::std::primitive::usize = #field_count_lit;

                // For each required field, generate a "visited" boolean flag
                #(#visited_field_declarations)*

                for (name, typ) in fields {
                    // Pattern match on the name and verify that the type is correct.
                    match name.as_str() {
                        #(#field_names => #type_check_blocks,)*
                        unknown => {
                            return ::std::result::Result::Err(
                                #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                                    ::std::format!("Unknown field: {}", unknown),
                                ),
                            )
                        }
                    }
                }

                if remaining_required_fields > 0 {
                    // If there are some missing required fields, generate an error
                    // which contains missing field names
                    let mut missing_fields = ::std::vec::Vec::<&'static str>::with_capacity(remaining_required_fields);
                    #(#append_name_blocks)*
                    return ::std::result::Result::Err(
                        #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                            ::std::format!("Missing fields: {:?}", missing_fields),
                        ),
                    )
                }

                ::std::result::Result::Ok(())
            }
        }
    }
}

struct DeserializeUnorderedGenerator<'sd>(&'sd StructDesc);

impl<'sd> DeserializeUnorderedGenerator<'sd> {
    // An identifier for a variable that is meant to store the parsed variable
    // before being ultimately moved to the struct on deserialize
    fn deserialize_field_variable(field: &Field) -> syn::Ident {
        quote::format_ident!("f_{}", field.ident.as_ref().unwrap().unraw())
    }

    // Generates an expression which produces a value ready to be put into a field
    // of the target structure
    fn generate_finalize_field(&self, field: &Field) -> syn::Expr {
        if field.skip {
            // Skipped fields are initialized with Default::default()
            return parse_quote!(::std::default::Default::default());
        }

        let crate_path = self.0.struct_attrs().crate_path();
        let deserialize_field = Self::deserialize_field_variable(field);
        if field.default_when_missing {
            // Generate Default::default if the field was missing
            parse_quote!(#deserialize_field.unwrap_or_default())
        } else {
            let cql_name_literal = field.cql_name_literal();
            parse_quote!(#deserialize_field.ok_or_else(|| {
                #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                    ::std::format!("Missing field: {}", #cql_name_literal)
                )
            })?)
        }
    }

    // Generated code that performs deserialization when the raw field
    // is being processed
    fn generate_deserialization(&self, field: &Field) -> Option<syn::Expr> {
        if field.skip {
            return None;
        }

        let crate_path = self.0.struct_attrs().crate_path();
        let constraint_lifetime = self.0.constraint_lifetime();
        let deserialize_field = Self::deserialize_field_variable(field);
        let cql_name_literal = field.cql_name_literal();
        let deserializer = field.deserialize_target();
        Some(parse_quote!(
            {
                if #deserialize_field.is_some() {
                    return ::std::result::Result::Err(
                        #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                            ::std::format!("Field {} occurs more than once in serialized data", #cql_name_literal),
                        ),
                    );
                } else {
                    // The value can be either
                    // - None - missing from the serialized representation
                    // - Some(None) - present in the serialized representation but null
                    // For now, we treat both cases as "null".
                    let value = value.flatten();
                    #deserialize_field = ::std::option::Option::Some(
                        <#deserializer as #crate_path::types::deserialize::value::DeserializeCql<#constraint_lifetime>>::deserialize(typ, value)?
                    );
                }
            }
        ))
    }

    // Generate a declaration of a variable that temporarily keeps
    // the deserialized value
    fn generate_deserialize_field_decl(field: &Field) -> Option<syn::Stmt> {
        if field.skip {
            return None;
        }
        let deserialize_field = Self::deserialize_field_variable(field);
        Some(parse_quote!(let mut #deserialize_field = ::std::option::Option::None;))
    }

    fn generate(&self) -> syn::ImplItemMethod {
        let crate_path = self.0.struct_attrs().crate_path();
        let constraint_lifetime = self.0.constraint_lifetime();
        let fields = self.0.fields();

        let deserialize_field_decls = fields.iter().map(Self::generate_deserialize_field_decl);
        let deserialize_blocks = fields.iter().flat_map(|f| self.generate_deserialization(f));
        let field_idents = fields.iter().map(|f| f.ident.as_ref().unwrap());
        let field_names = fields
            .iter()
            .filter(|f| !f.skip)
            .map(|f| f.cql_name_literal());

        let field_finalizers = fields.iter().map(|f| self.generate_finalize_field(f));

        let iterator_type =
            quote!(#crate_path::types::deserialize::value::UdtIterator<#constraint_lifetime>);

        // TODO: Allow collecting unrecognized fields into some special field

        parse_quote! {
            fn deserialize(
                typ: &#constraint_lifetime #crate_path::frame::response::result::ColumnType,
                v: ::std::option::Option<#crate_path::types::deserialize::FrameSlice<#constraint_lifetime>>,
            ) -> ::std::result::Result<Self, #crate_path::frame::frame_errors::ParseError> {
                // Create an iterator over the fields of the UDT.
                let iter = <#iterator_type as #crate_path::types::deserialize::value::DeserializeCql<#constraint_lifetime>>::deserialize(typ, v)?;

                // Generate fields that will serve as temporary storage
                // for the fields' values. Those are of type Option<FieldType>.
                #(#deserialize_field_decls)*

                for item in iter {
                    let ((name, typ), value) = item?;
                    // Pattern match on the field name and deserialize.
                    match name.as_str() {
                        #(#field_names => #deserialize_blocks,)*
                        unknown => return ::std::result::Result::Err(
                            #crate_path::frame::frame_errors::ParseError::BadIncomingData(
                                format!("Unknown field: {}", unknown),
                            )
                        )
                    }
                }

                // Create the final struct. The finalizer expressions convert
                // the temporary storage fields to the final field values.
                // For example, if a field is missing but marked as
                // `default_when_null` it will create a default value, otherwise
                // it will report an error.
                Ok(Self {
                    #(#field_idents: #field_finalizers,)*
                })
            }
        }
    }
}
