use super::AST::{self};
use std::path::Path;
use super::super::scanner::scanner::scan_file;
use std::collections::HashMap;
use super::parser_printer::ParserPrinter;

#[derive(Clone)]
#[derive(Debug)]
#[derive(PartialEq)]
enum TokenType {
    Symbol, // either a keyword or one char symbol
    Char, 
    String,
    Int,
    Long,
    Bool,
    Identifier,
    EOF,
}

#[derive(Clone)]
#[derive(Debug)]
struct Token {
    token_type: TokenType,
    token_value: String,
    line_num: String,
}

struct ParserState {
    tokens: Vec<Token>,
    token_idx: usize, 
}

impl ParserState {
    fn cur_token(&self) -> Token {
        return self.tokens[self.token_idx].clone();
    }

    fn consume(&mut self) {
        self.token_idx += 1;
    }

    fn check_token(&mut self, comp_token: &str, consume: bool) -> Result<(), String> {
        if self.cur_token().token_value != comp_token {
            return Err(format!("Line: {} - Expected token: {}, got: {}", 
                       self.cur_token().line_num, comp_token, self.cur_token().token_value));
        }
        if consume { // we have consume as a parameter in case we need to store the value of the current token after checking
            self.consume(); 
        }
        return Ok(());
    }

    fn check_multiple_tokens(&mut self, comp_tokens: Vec<&str>, consume: bool) -> Result<(), String> {
        if comp_tokens.contains(&self.cur_token().token_value.as_str()) {
            if consume {
                self.consume();
            }
            return Ok(());
        }
        return Err(format!("Line: {} - Expected one of: {:?}, got: {}", 
                            self.cur_token().line_num, comp_tokens, self.cur_token().token_value));
    }

    fn check_incr_token(&mut self, comp_token: &str, incr_index: usize) -> bool {
        if self.token_idx + incr_index >= self.tokens.len() {
            return false;
        }
        return self.tokens[self.token_idx + incr_index].token_value == comp_token;
    }
}

// helper functions
fn split_token(token_str: &str) -> Vec<&str> {
    let mut parts = vec![];
    let mut end_ind = 0;
    for (i, c) in token_str.char_indices() {
        if c.is_whitespace() {
            if i > 0 {
                parts.push(&token_str[end_ind..i]);
            }
            end_ind = i + 1;
            if parts.len() == 2 {
                break;
            }
        }
    }
    parts.push(&token_str[end_ind..]);
    return parts;
}

fn unpack_token(symbol_text: &str) -> Token {
    let parts: Vec<&str> = split_token(symbol_text);
    let type_map: HashMap<&str, TokenType> = HashMap::from([
        ("IDENTIFIER", TokenType::Identifier),
        ("INTLITERAL", TokenType::Int),
        ("LONGLITERAL", TokenType::Long),
        ("STRINGLITERAL", TokenType::String),
        ("CHARLITERAL", TokenType::Char),
        ("BOOLEANLITERAL", TokenType::Bool),
    ]);

    match parts[1] {
        "IDENTIFIER" | "CHARLITERAL" | "STRINGLITERAL" | "BOOLEANLITERAL" | "INTLITERAL" | "LONGLITERAL" => { 
            return Token {
                token_type: type_map.get(parts[1]).unwrap().clone(),
                token_value: parts[2].to_string(),
                line_num: parts[0].to_string(),
            }
        },
        _ => {
            return Token {
                token_type: TokenType::Symbol,
                token_value: parts[1].to_string(),
                line_num: parts[0].to_string(),
            }
        }
    }
}

// parse functions for each grammar rule

fn parse_int_literal(parser_state: &mut ParserState, is_neg: bool) -> Result<AST::IntConstant, String> {
    match parser_state.cur_token().token_type {
        TokenType::Int => {
            let int_val = AST::IntConstant {
                is_neg: is_neg,
                value: parser_state.cur_token().token_value.clone(),
            };
            parser_state.consume();
            return Ok(int_val);
        },
        _ => return Err(format!("Line: {} - Expected int literal, got: {:?}", 
                                parser_state.cur_token().line_num, parser_state.cur_token().token_value)),
    }
}

fn parse_long_literal(parser_state: &mut ParserState, is_neg: bool) -> Result<AST::LongConstant, String> {
    match parser_state.cur_token().token_type {
        TokenType::Long => {
            let mut long_val = parser_state.cur_token().token_value.clone();
            if long_val.chars().last().unwrap() == 'L' {
                long_val.pop();
            }
            let long_val = AST::LongConstant {
                is_neg: is_neg,
                value: long_val,
            };
            parser_state.consume();
            return Ok(long_val);
        },
        _ => return Err(format!("Line: {} - Expected long literal, got: {:?}", 
                                parser_state.cur_token().line_num, parser_state.cur_token().token_value)),
    }
}

fn parse_char_literal(parser_state: &mut ParserState) -> Result<AST::CharConstant, String> {
    match parser_state.cur_token().token_type {
        TokenType::Char => {
            let extract_char = parser_state.cur_token().token_value.clone();
            let char_val = AST::CharConstant {
                value: extract_char[1..extract_char.len()-1].to_string(),
            };
            parser_state.consume();
            return Ok(char_val);
        },
        _ => return Err(format!("Line: {} - Expected char literal, got: {:?}", 
                                parser_state.cur_token().line_num, parser_state.cur_token().token_value)),
    }
}

fn parse_bool_literal(parser_state: &mut ParserState) -> Result<AST::BoolConstant, String> {
    match parser_state.cur_token().token_type {
        TokenType::Bool => {
            let bool_val = AST::BoolConstant {
                value: parser_state.cur_token().token_value == "true",
            };
            parser_state.consume();
            return Ok(bool_val);
        },
        _ => return Err(format!("Line: {} - Expected bool literal, got: {:?}", 
                                parser_state.cur_token().line_num, parser_state.cur_token().token_value)),
    }
}

fn parse_string_literal(parser_state: &mut ParserState) -> Result<AST::StringConstant, String> {
    match parser_state.cur_token().token_type {
        TokenType::String => {
            let string_val = AST::StringConstant {
                value: parser_state.cur_token().token_value.clone(),
            };
            parser_state.consume();
            return Ok(string_val);
        },
        _ => return Err(format!("Line: {} - Expected string literal, got: {:?}", 
                                parser_state.cur_token().line_num, parser_state.cur_token().token_value)),
    }
}

fn parse_literal(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    let mut is_neg = false;
    if parser_state.cur_token().token_value == "-" {
        parser_state.consume();
        is_neg = true;
    }
    match parser_state.cur_token().token_type {
        TokenType::Int => {
            return Ok(AST::ASTNode::IntConstant(parse_int_literal(parser_state, is_neg)?));
        },
        TokenType::Long => {
            return Ok(AST::ASTNode::LongConstant(parse_long_literal(parser_state, is_neg)?));
        },
        TokenType::Char => {
            // TODO: remove this if this violates test cases since technically we shouldn't be doing this
            if is_neg {
                return Err(format!("Line: {} - Error - can't have negative sign in front of char literal", parser_state.cur_token().line_num));
            }
            return Ok(AST::ASTNode::CharConstant(parse_char_literal(parser_state)?));
        },
        TokenType::Bool => {
            if is_neg {
                return Err(format!("Line: {} - Error - can't have negative sign in front of bool literal", parser_state.cur_token().line_num));
            }
            return Ok(AST::ASTNode::BoolConstant(parse_bool_literal(parser_state)?));
        },
        _ => return Err(format!("Line: {} - Expected literal (char, int, bool), got: {:?}", 
                                parser_state.cur_token().line_num, parser_state.cur_token().token_value)),
    }  
}

fn parse_identifier(parser_state: &mut ParserState, status: i32) -> Result<AST::Identifier, String> {
    match parser_state.cur_token().token_type {
        TokenType::Identifier => {
            let id = AST::Identifier {
                name: parser_state.cur_token().token_value.clone(),
                status: status,
            };
            parser_state.consume();
            return Ok(id);
        },
        _ => return Err(format!("Line: {} - Expected identifier, got: {:?}", parser_state.cur_token().line_num, parser_state.cur_token().token_value)),
    }
}

fn parse_location(parser_state: &mut ParserState, status: i32) -> Result<AST::ASTNode, String> {
    let id = parse_identifier(parser_state, status)?;
    if parser_state.cur_token().token_value == "[" {
        parser_state.consume();
        let idx_expr = parse_expression(parser_state)?;
        parser_state.check_token("]", true)?;
        return Ok(AST::ASTNode::IndexExpression(AST::IndexExpression {
            id: Box::new(id),
            idx_expr: Box::new(idx_expr),
        }));
    } else {
        return Ok(AST::ASTNode::Identifier(id));
    }
}

fn parse_method_call(parser_state: &mut ParserState) -> Result<AST::MethodCall, String> {
    let method_name = parse_identifier(parser_state, 1)?;
    parser_state.check_token("(", true)?;
    let mut args: Vec<Box<AST::ASTNode>> = vec![];
    if parser_state.cur_token().token_value != ")" {
        loop {
            if parser_state.cur_token().token_type == TokenType::String {
                args.push(Box::new(AST::ASTNode::StringConstant(parse_string_literal(parser_state)?)));
            } else {
                args.push(Box::new(parse_expression(parser_state)?));
            }

            if parser_state.check_token(",", true) != Ok(()) {
                break;
            }
        }
    }
    parser_state.check_token(")", true)?;
    return Ok(AST::MethodCall {
        name: Box::new(method_name),
        args: args,
    });
}


fn parse_stand_alone_expr(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    match parser_state.cur_token().token_value.as_str() {
        "len" => {
            parser_state.consume();
            parser_state.check_token("(", true)?;
            let id = parse_identifier(parser_state, 1)?;
            parser_state.check_token(")", true)?;
            return Ok(AST::ASTNode::LenCall(AST::LenCall {
                id: Box::new(id),
            }))
        },
       "(" => {
            parser_state.consume();
            let expr = parse_expression(parser_state)?;
            parser_state.check_token(")", true)?;
            return Ok(expr)
        },
        "-" => {
            parser_state.consume();
            // try to parse expression as integer literal
            match parser_state.cur_token().token_type {
                TokenType::Int => {
                    return Ok(AST::ASTNode::IntConstant(parse_int_literal(parser_state, true)?));
                },
                TokenType::Long => {
                    return Ok(AST::ASTNode::LongConstant(parse_long_literal(parser_state, true)?));
                },
                _ => {
                    let expr = parse_stand_alone_expr(parser_state)?;
                    return Ok(AST::ASTNode::UnaryExpression(AST::UnaryExpression {
                        op: "-".to_string(),
                        expr: Box::new(expr),
                    }))
 
                }
            }
        },
        "!" => {
            parser_state.consume();
            let expr = parse_stand_alone_expr(parser_state)?;
            return Ok(AST::ASTNode::UnaryExpression(AST::UnaryExpression {
                op: "!".to_string(),
                expr: Box::new(expr),
            }))
        },
        _ => {
            // Handle identifier-based expressions (location or method_call) and literals
            match parser_state.cur_token().token_type {
                TokenType::Int | TokenType::Char | TokenType::Bool | TokenType::Long => {
                    parse_literal(parser_state)
                },
                TokenType::Identifier => {
                    let saved_token_idx = parser_state.token_idx;
                    match parse_method_call(parser_state) {
                        Ok(method_call) => Ok(AST::ASTNode::MethodCall(method_call)), 
                        Err(_) => {
                            parser_state.token_idx = saved_token_idx;
                            return parse_location(parser_state, 1);
                        }
                    }
                },
                _ => Err(format!("Line: {} - Invalid token in expression: {:?}", 
                    parser_state.cur_token().line_num, 
                    parser_state.cur_token().token_value))
            }
        }
    }
}

fn parse_cast_expr(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    match parser_state.cur_token().token_value.as_str() {
        "int" => {
            parser_state.consume();
            parser_state.check_token("(", true)?;
            let cast_expr = parse_expression(parser_state)?;
            parser_state.check_token(")", true)?;
            return Ok(AST::ASTNode::IntCast(AST::IntCast {
                cast_expr: Box::new(cast_expr),
            }))
        },
        "long" => {
            parser_state.consume();
            parser_state.check_token("(", true)?;
            let cast_expr = parse_expression(parser_state)?;
            parser_state.check_token(")", true)?;
            return Ok(AST::ASTNode::LongCast(AST::LongCast {
                cast_expr: Box::new(cast_expr),
            }))
        },
 
        _ => {
            return parse_stand_alone_expr(parser_state);
        }
    }
}

fn parse_mul_op_expr(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    let mut left = parse_cast_expr(parser_state)?;
    while ["*", "/", "%"].contains(&parser_state.cur_token().token_value.as_str()) {
        let op = parser_state.cur_token().token_value.clone();
        parser_state.consume();
        let right = parse_cast_expr(parser_state)?;
        left = AST::ASTNode::BinaryExpression(AST::BinaryExpression {
            op,
            left_expr: Box::new(left),
            right_expr: Box::new(right),
        });
    }
    return Ok(left);
}

fn parse_add_op_expr(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    let mut left = parse_mul_op_expr(parser_state)?;
    while ["+", "-"].contains(&parser_state.cur_token().token_value.as_str()) {
        let op = parser_state.cur_token().token_value.clone();
        parser_state.consume();
        let right = parse_mul_op_expr(parser_state)?;
        left = AST::ASTNode::BinaryExpression(AST::BinaryExpression {
            op,
            left_expr: Box::new(left),
            right_expr: Box::new(right),
        });
    }
    return Ok(left);
}

fn parse_comparison_expr(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    let mut left = parse_add_op_expr(parser_state)?;
    while ["<", "<=", ">", ">="].contains(&parser_state.cur_token().token_value.as_str()) {
        let op = parser_state.cur_token().token_value.clone();
        parser_state.consume();
        let right = parse_add_op_expr(parser_state)?;
        left = AST::ASTNode::BinaryExpression(AST::BinaryExpression {
            op,
            left_expr: Box::new(left),
            right_expr: Box::new(right),
        });
    }
    return Ok(left);
}

fn parse_equality_expr(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    let mut left = parse_comparison_expr(parser_state)?;
    while ["!=", "=="].contains(&parser_state.cur_token().token_value.as_str()) {
        let op = parser_state.cur_token().token_value.clone();
        parser_state.consume();
        let right = parse_comparison_expr(parser_state)?;
        left = AST::ASTNode::BinaryExpression(AST::BinaryExpression {
            op,
            left_expr: Box::new(left),
            right_expr: Box::new(right),
        });
    }
    return Ok(left);
}

fn parse_and_operator(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    let mut left = parse_equality_expr(parser_state)?;
    while parser_state.cur_token().token_value == "&&" {
        parser_state.consume();
        let right = parse_equality_expr(parser_state)?;
        left = AST::ASTNode::BinaryExpression(AST::BinaryExpression {
            op: "&&".to_string(),
            left_expr: Box::new(left),
            right_expr: Box::new(right),
        });
    }
    return Ok(left);
}

fn parse_or_operator(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    let mut left = parse_and_operator(parser_state)?;
    while parser_state.cur_token().token_value == "||" {
        parser_state.consume();
        let right = parse_and_operator(parser_state)?;
        left = AST::ASTNode::BinaryExpression(AST::BinaryExpression {
            op: "||".to_string(),
            left_expr: Box::new(left),
            right_expr: Box::new(right),
        });
    }
    return Ok(left);
}

// Main entry point for expressions
fn parse_expression(parser_state: &mut ParserState) -> Result<AST::ASTNode, String> {
    return parse_or_operator(parser_state);
}

fn parse_assign_expression(parser_state: &mut ParserState) -> Result<AST::Assignment, String> {
    let op = parser_state.cur_token().token_value;
    let default_var_name = "".to_string();
    match op.as_str() {
        "++" | "--" => {
            parser_state.consume();
            return Ok(AST::Assignment {
                assign_var: Box::new(AST::ASTNode::Identifier(AST::Identifier { name: default_var_name, status: 2 })),
                assign_op: op,
                expr: Box::new(None),
            });
        },
        "=" | "+=" | "-=" | "*=" | "/=" | "%=" => {
            parser_state.consume();
            let assign_expr = parse_expression(parser_state)?;
            return Ok(AST::Assignment {
                assign_var: Box::new(AST::ASTNode::Identifier(AST::Identifier { name: default_var_name, status: 2 })),
                assign_op: op,
                expr: Box::new(Some(assign_expr)),
            });
        },
        _ => {
            return Err(format!("Line: {} - Error - incorrect operator symbol, got: {:?}", parser_state.cur_token().line_num, parser_state.cur_token().token_value));
        }
    }
}

fn parse_if_statement(parser_state: &mut ParserState, func_type: &str) -> Result<AST::IfStatement, String> {
    parser_state.check_token("if", true)?;
    parser_state.check_token("(", true)?;
    let condition_expr = parse_expression(parser_state)?;
    parser_state.check_token(")", true)?;
    let then_block = parse_block(parser_state, func_type)?;
    let mut else_block: Option<AST::Block> = None;
    if parser_state.check_token("else", true) == Ok(()) {
        else_block = Some(parse_block(parser_state, func_type)?);
    }
    return Ok(AST::IfStatement {
        condition: Box::new(condition_expr),
        then_block: Box::new(then_block),
        else_block: Box::new(else_block),
    });
}

fn parse_for_statement(parser_state: &mut ParserState, func_type: &str) -> Result<AST::ForStatement, String> {
    parser_state.check_token("for", true)?;
    parser_state.check_token("(", true)?;
    let increment_var = parse_identifier(parser_state, 2)?;
    parser_state.check_token("=", true)?;
    let start_expr = parse_expression(parser_state)?;
    parser_state.check_token(";", true)?;
    let end_expr = parse_expression(parser_state)?;
    parser_state.check_token(";", true)?;

    let start_assignment = AST::Assignment {
        assign_var: Box::new(AST::ASTNode::Identifier(increment_var)),
        assign_op: "=".to_string(),
        expr: Box::new(Some(start_expr)),
    };
    
    // parse for_update rule 
    let update_expr: AST::ASTNode;
    let saved_token_idx = parser_state.token_idx;
    match parse_method_call(parser_state) {
        Ok(method_call) => {
            update_expr = AST::ASTNode::MethodCall(method_call);
        },
        Err(_) => {
            parser_state.token_idx = saved_token_idx;
            let update_assign_var = parse_location(parser_state, 2)?;
            let mut update_assign_expr = parse_assign_expression(parser_state)?;
            update_assign_expr.assign_var = Box::new(update_assign_var);
            update_expr = AST::ASTNode::Assignment(update_assign_expr);
        }
    }

    // parse block
    parser_state.check_token(")", true)?;
    let block = parse_block(parser_state, func_type)?;

    return Ok(AST::ForStatement {
        start_assignment: Box::new(start_assignment),
        end_expr: Box::new(end_expr),
        update_expr: Box::new(update_expr),
        block: Box::new(block),
    });
}

fn parse_while_statement(parser_state: &mut ParserState, func_type: &str) -> Result<AST::WhileStatement, String> {
    parser_state.check_token("while", true)?;
    parser_state.check_token("(", true)?;
    let condition_expr = parse_expression(parser_state)?;
    parser_state.check_token(")", true)?;
    let block = parse_block(parser_state, func_type)?;
    return Ok(AST::WhileStatement {
        condition: Box::new(condition_expr),
        block: Box::new(block),
    });
}

fn parse_return_statement(parser_state: &mut ParserState, func_type: &str) -> Result<AST::ReturnStatement, String> {
    parser_state.check_token("return", true)?;
    let mut return_statement_res= AST::ReturnStatement {
        func_type: func_type.to_string(),
        expr: Box::new(None)
    };
    if parser_state.cur_token().token_value != ";" {
        return_statement_res.expr = Box::new(Some(parse_expression(parser_state)?));
    }
    parser_state.check_token(";", true)?;
    return Ok(return_statement_res);
}

fn parse_break_statement(parser_state: &mut ParserState) -> Result<AST::StatementControl, String> {
    parser_state.check_token("break", true)?;
    parser_state.check_token(";", true)?;
    return Ok(AST::StatementControl {
        op: "break".to_string(),
    });
}

fn parse_continue_statement(parser_state: &mut ParserState) -> Result<AST::StatementControl, String> {
    parser_state.check_token("continue", true)?;
    parser_state.check_token(";", true)?;
    return Ok(AST::StatementControl {
        op: "continue".to_string(),
    });
}

fn parse_statement(parser_state: &mut ParserState, func_type: &str) -> Result<AST::ASTNode, String> {
    match parser_state.cur_token().token_value.as_str() {
        "if" => {
            return Ok(AST::ASTNode::IfStatement(parse_if_statement(parser_state, func_type)?));
        },
        "for" => {
            return Ok(AST::ASTNode::ForStatement(parse_for_statement(parser_state, func_type)?));
        },
        "while" => {
            return Ok(AST::ASTNode::WhileStatement(parse_while_statement(parser_state, func_type)?));
        },
        "return" => {
            return Ok(AST::ASTNode::ReturnStatement(parse_return_statement(parser_state, func_type)?));
        },
        "break" => {
            return Ok(AST::ASTNode::StatementControl(parse_break_statement(parser_state)?));
        },
        "continue" => {
            return Ok(AST::ASTNode::StatementControl(parse_continue_statement(parser_state)?));
        },
        _ => {
            let saved_token_idx = parser_state.token_idx;
            match parse_method_call(parser_state) {
                Ok(method_call) => {
                    let method_call_res = Ok(AST::ASTNode::MethodCall(method_call));
                    parser_state.check_token(";", true)?;
                    return method_call_res;
                },
                Err(_) => {
                    parser_state.token_idx = saved_token_idx;
                    let assign_var = parse_location(parser_state, 2)?;
                    let mut assign_expr = parse_assign_expression(parser_state)?;
                    assign_expr.assign_var = Box::new(assign_var);
                    parser_state.check_token(";", true)?;
                    return Ok(AST::ASTNode::Assignment(assign_expr));
                }
            }
        }
    }
}

fn parse_block(parser_state: &mut ParserState, func_type: &str) -> Result<AST::Block, String> {
    parser_state.check_token("{", true)?;
    let mut block = AST::Block {
        fields: vec![],
        statements: vec![],
    };
    // consume field declarations
    while ["int", "bool", "const", "long"].contains(&parser_state.cur_token().token_value.as_str()) {
        let field_decl = parse_field_decl(parser_state)?;
        block.fields.push(Box::new(field_decl));
    }
    // consume statements
    while parser_state.cur_token().token_value != "}" {
        let statement = parse_statement(parser_state, func_type)?;
        block.statements.push(Box::new(statement));
    }
    parser_state.check_token("}", true)?;
    return Ok(block);
}

fn parse_import_decl(parser_state: &mut ParserState) -> Result<AST::ImportDecl, String> {
    parser_state.check_token("import", true)?;
    let import_id = parse_identifier(parser_state, 0)?;
    parser_state.check_token(";", true)?;
    return Ok(AST::ImportDecl { 
        import_id: import_id,
    });
}

fn parse_field_decl(parser_state: &mut ParserState) -> Result<AST::FieldDecl, String> {
    // consume const if it exists
    let mut is_const = false;
    if parser_state.cur_token().token_value == "const" {
        parser_state.consume();
        is_const = true;
    }

    // consume type
    parser_state.check_multiple_tokens(vec!["int", "bool", "long"], false)?;
    let field_type = parser_state.cur_token().token_value.clone();
    parser_state.consume();

    // consume identifiers
    let mut vars: Vec<Box<AST::VarDecl>> = vec![];
    
    loop {
        let var_id = parse_identifier(parser_state, 0)?;
        let mut is_array = false;
        let mut array_len: Option<AST::IntConstant> = None;
        let initializer: Option<AST::ASTNode> = None;

        // case if we have id[int] initializer
        if parser_state.cur_token().token_value.clone() == "[" {
            parser_state.consume();
            if parser_state.cur_token().token_value != "]" {
                array_len = Some(parse_int_literal(parser_state, false)?);
            }
            parser_state.check_token("]", true)?;
            is_array = true;
        }
        
        // add new var to array
        vars.push(Box::new(AST::VarDecl {
            name: Box::new(var_id),
            is_const: is_const,
            type_name: field_type.clone(),
            is_array: is_array,
            array_len: Box::new(array_len),
            initializer: Box::new(initializer),
        }));

        if parser_state.check_token(",", true) != Ok(()) {
            break;
        }
    }
    parser_state.check_token(";", true)?;
    return Ok(AST::FieldDecl {
        type_name: field_type,
        is_const: is_const,
        vars: vars,
    });   
}

fn parse_method_decl(parser_state: &mut ParserState) -> Result<AST::MethodDecl, String> {
    // consume method type
    parser_state.check_multiple_tokens(vec!["int", "bool", "long", "void"], false)?;
    let method_type = parser_state.cur_token().token_value.clone();
    parser_state.consume();
    let method_name = parse_identifier(parser_state, 0)?;
    parser_state.check_token("(", true)?;
    let mut args: Vec<Box<AST::MethodArgDecl>> = vec![];

    // parse args
    if vec!["int", "bool", "long"].contains(&parser_state.cur_token().token_value.as_str()) {
        loop {
            parser_state.check_multiple_tokens(vec!["int", "bool", "long"], false)?;
            let arg_type = parser_state.cur_token().token_value.clone();
            parser_state.consume();
            let arg_name = parse_identifier(parser_state, 0)?;
            args.push(Box::new(AST::MethodArgDecl {
                type_name: arg_type,
                name: Box::new(arg_name),
            }));
            if parser_state.check_token(",", true) != Ok(()) {
                break;
            } 
        }
    }
    
    parser_state.check_token(")", true)?;
    let method_block = parse_block(parser_state, method_type.as_str())?;
    return Ok(AST::MethodDecl {
        type_name: method_type,
        name: method_name,
        args: args,
        body: Box::new(method_block),
    });
}

fn parse_program(parser_state: &mut ParserState) -> Result<AST::Program, String> {
    let mut program = AST::Program {
        imports: vec![],
        fields: vec![],
        methods: vec![],
    };

    // consume imports
    while parser_state.cur_token().token_value == "import" {
        let import_id = parse_import_decl(parser_state)?;
        program.imports.push(Box::new(import_id));
    }

    // consume field declarations
    while ["int", "bool", "long", "const"].contains(&parser_state.cur_token().token_value.as_str()) && 
            !parser_state.check_incr_token("(", 2) {
        
        let field_decl = parse_field_decl(parser_state)?;
        program.fields.push(Box::new(field_decl));
    }

    // consume method declarations
    while ["int", "bool", "long", "void"].contains(&parser_state.cur_token().token_value.as_str()) {
        let method_decl = parse_method_decl(parser_state)?;
        program.methods.push(Box::new(method_decl));
    }

    // end check
    if parser_state.cur_token().token_value != "EOF" {
        return Err(format!("Line: {} - Error - expected EOF, got: {:?}", parser_state.cur_token().line_num, parser_state.cur_token().token_value));
    }

    return Ok(program);
}

pub fn parse_file(file_path: &Path) -> Result<AST::Program, Vec<String>> {
    // Lex file first
    match scan_file(file_path) {
        Ok(tokens) => {    
            let mut parser_state = ParserState {
                tokens: tokens.iter().map(|x| unpack_token(x.as_str())).collect(),
                token_idx: 0,
            };
            // Add EOF token
            parser_state.tokens.push(Token {
                token_type: TokenType::EOF,
                token_value: "EOF".to_string(),
                line_num: "".to_string(),
            });
            match parse_program(&mut parser_state) {
                Ok(parsed_program) => return Ok(parsed_program),
                Err(e) => return Err(vec![e])
            }
        }, 
        Err(e) => return Err(e)
    }
}

pub fn parse(file_path: &Path, mut writer: Box<dyn std::io::Write>, debug: bool) {
    match parse_file(file_path) {
        Ok(parsed_program) => {
            writeln!(writer, "Parsed file: {:?} \n", file_path.display()).unwrap();
            if debug {
                let mut pretty_printer = ParserPrinter::new();
                parsed_program.accept(&mut pretty_printer);
            }
            std::process::exit(0);
        },
        Err(errors) => {
            for error in errors {
                if let Err(e) = writeln!(writer, "{}", error) {
                    eprintln!("Failed to write token to output: {}", e);
                }
            }
            std::process::exit(1);
        }
    }
}   
