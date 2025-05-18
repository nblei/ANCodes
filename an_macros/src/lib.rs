use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote};
use syn::{parse_macro_input, LitInt};

/// Generates a distance function implementation for AN codes.
///
/// This macro generates a function that checks for errors at a specific Hamming distance.
/// The generated function follows the pattern seen in AnCode::distance1, distance2, etc.
/// with nested loops to check all possible combinations of bit positions.
#[proc_macro]
pub fn define_distance_fn(input: TokenStream) -> TokenStream {
    // Parse the input distance value (e.g., 1, 2, 3, etc.)
    let distance = parse_macro_input!(input as LitInt);
    let distance_value = distance.base10_parse::<usize>().unwrap();

    // Generate the function implementation
    let expanded = generate_distance_fn(distance_value);

    // Return the generated TokenStream
    expanded.into()
}

fn generate_distance_fn(dist: usize) -> TokenStream2 {
    let fn_name = format_ident!("distance{}", dist);

    // Generate alpha extractions
    let alpha_extracts = (1..=dist)
        .map(|i| {
            let var_name = format_ident!("a{}", i);
            let shift = i - 1;
            quote! { let #var_name = (alpha >> #shift) & 1; }
        })
        .collect::<Vec<_>>();

    // Generate the nested loops structure
    let inner_body = generate_nested_structure(dist);

    // Generate the complete function
    quote! {
        fn #fn_name(&mut self) {
            const DIST: usize = #dist;
            let bases = get_bases::<u64>();
            for alpha in 0..(1 << DIST) {
                #(#alpha_extracts)*
                #inner_body
            }
        }
    }
}

fn generate_nested_structure(dist: usize) -> TokenStream2 {
    let mut current = if dist == 1 {
        // Special case for distance 1 (no nesting)
        quote! {
            let val = val1 as u64;
            if val % self.a == 0 {
                self.add_error(val, DIST - 1);
            }
        }
    } else {
        // Final check for divisibility
        let val_var = format_ident!("val{}", dist);
        quote! {
            let val = #val_var as u64;
            if val % self.a == 0 {
                self.add_error(val, DIST - 1);
            }
        }
    };

    // Build loops from innermost to outermost
    for level in (1..=dist).rev() {
        let i_var = format_ident!("i{}", level);
        let a_var = format_ident!("a{}", level);
        let val_var = format_ident!("val{}", level);

        if level == 1 {
            // Outermost loop
            current = quote! {
                for #i_var in 0..64 {
                    let #val_var = bases[#a_var][#i_var];
                    #current
                }
            };
        } else {
            // Inner loops with dependency on previous loop
            let prev_i = format_ident!("i{}", level - 1);
            let prev_val = format_ident!("val{}", level - 1);

            current = quote! {
                for #i_var in (#prev_i + 1)..64 {
                    let #val_var = bases[#a_var][#i_var].wrapping_add(#prev_val);
                    #current
                }
            };
        }
    }

    current
}

