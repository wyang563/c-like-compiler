
const RESERVED_LITERALS: &'static [&str] = &[
    "bool",
    "break",
    "const",
    "import",
    "continue",
    "else",
    "false",
    "for",
    "while",
    "if",
    "int",
    "return",
    "len",
    "long",
    "true",
    "void"
];

pub fn is_whitespace(c: char) -> bool {
    let whitespace = "\n\r\t ";
    return whitespace.contains(c);
}

pub fn is_alphabetic(c: char) -> bool {
    let letters = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
    return letters.contains(c);
}

pub fn is_valid_symbol(c: char) -> bool {
    let symbols = "-+*/%<>=!&|()[];,{}";
    return symbols.contains(c);
}

pub fn is_hex(c: char) -> bool {
    let hex = "0123456789abcdefABCDEF";
    return hex.contains(c);
}

pub fn is_numeric(c: char) -> bool {
    let numbers = "0123456789";
    return numbers.contains(c);
}

pub fn is_alphanumeric(c: char) -> bool {
    return is_alphabetic(c) || is_numeric(c);
}

pub fn is_reserved_literal(c: &str) -> bool {
    return RESERVED_LITERALS.contains(&c);
}

