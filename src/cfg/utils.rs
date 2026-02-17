use super::three_address_code::{BinOp, ValueId};

/// Process a string literal value from the parser (which includes surrounding quotes
/// and raw escape sequences like \n, \t, \\) into actual bytes.
pub fn process_string_literal(raw: &str) -> Vec<i8> {
    // Strip surrounding quotes
    let inner = if raw.starts_with('"') && raw.ends_with('"') && raw.len() >= 2 {
        &raw[1..raw.len() - 1]
    } else {
        raw
    };

    let mut bytes = Vec::new();
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            match chars.next() {
                Some('n') => bytes.push(b'\n' as i8),
                Some('t') => bytes.push(b'\t' as i8),
                Some('\\') => bytes.push(b'\\' as i8),
                Some('"') => bytes.push(b'"' as i8),
                Some('\'') => bytes.push(b'\'' as i8),
                Some('0') => bytes.push(0),
                Some(other) => {
                    // Unknown escape — emit backslash and the character
                    bytes.push(b'\\' as i8);
                    bytes.push(other as i8);
                }
                None => bytes.push(b'\\' as i8),
            }
        } else {
            bytes.push(ch as i8);
        }
    }
    bytes
}

/// Check if a value name is a generic instruction name (not a user variable).
/// Used to decide whether to propagate a variable name onto a value.
pub fn is_generic_value_name(name: &str) -> bool {
    name.is_empty()
        || matches!(
            name,
            "call" | "binop" | "cmp" | "neg" | "not" | "cast" | "len" | "logic" | "short_circuit"
        )
}

/// Map a compound assignment operator string to the corresponding BinOp.
pub fn compound_assign_to_binop(op: &str) -> BinOp {
    match op {
        "+=" | "++" => BinOp::Add,
        "-=" | "--" => BinOp::Sub,
        "*=" => BinOp::Mul,
        "/=" => BinOp::SDiv,
        "%=" => BinOp::SRem,
        _ => {
            eprintln!("Error: unsupported compound assignment operator: {}", op);
            panic!();
        }
    }
}

/// Look up a variable's value in a snapshot by (scope_ind, var_name).
pub fn lookup_snapshot_var(
    snapshot: &[(usize, String, ValueId)],
    scope_ind: usize,
    var_name: &str,
) -> ValueId {
    snapshot
        .iter()
        .find(|(s, n, _)| *s == scope_ind && n == var_name)
        .map(|(_, _, v)| *v)
        .unwrap()
}
