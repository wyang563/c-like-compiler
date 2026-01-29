use super::super::parser::visitor::{Visitor};
use super::super::semantics::symbol_table::{SymbolTable, Entry as SymEntry, Type as SymType};
use super::super::parser::AST;
use super::three_address_code::{ProgramIR, Symbol, GlobalDecl, GlobalKind, Type, ConstValue};
use std::collections::{HashSet, HashMap};

#[allow(non_camel_case_types)]
pub struct SSA_CFG_Compiler {
    // final output IR
    program_ir: ProgramIR,

    // variable/func tracking
    imported_funcs: HashSet<String>,

    // variable value id tracking by scope (need it by scope for SSA compliance across all non-global scopes)
    var_to_value_id: HashMap<usize, HashMap<String, u32>>,

    // tracking state (globally)
    cur_value_id: u32,
    cur_block_id: u32,
    cur_mem_id: u32,
    cur_scope_ind: usize,
    symbol_table: SymbolTable,
    
    // tracking state (per-scope)
    cur_child_scope_map: HashMap<usize, usize>, // map from parent scope idx to which child scope idx we're on

    // result store variables
    result_var_type: Type,
    result_is_global: Option<bool>, // tracks whether an identifier processed is a global
    result_literal_value: Option<ConstValue>,
    result_array_literal_values: Option<Vec<ConstValue>>
}

impl SSA_CFG_Compiler {
    // helpers for getting state
    fn get_cur_value_id(&mut self) -> u32 {
        self.cur_value_id += 1;
        return self.cur_value_id - 1
    }

    fn get_result_var_type(&mut self) -> Type {
        let result_type = self.result_var_type.clone();
        self.result_var_type = Type::None; // reset result var type for safety
        return result_type;
    }

    fn get_is_global(&mut self) -> bool {
        let is_global = self.result_is_global.unwrap();
        self.result_is_global = None; // reset result is global for safety
        return is_global;
    }

    fn get_literal_value(&mut self) -> ConstValue {
        let literal_value = self.result_literal_value.clone().unwrap();
        self.result_literal_value = None; // reset result literal value for safety
        return literal_value;
    }

    fn get_array_literal_values(&mut self) -> Vec<ConstValue> {
        let array_literal_values = self.result_array_literal_values.clone().unwrap();
        self.result_array_literal_values = None; // reset result array literal values for safety
        return array_literal_values;
    }

    // get entry from a given scope index
    fn get_scope_entry(&self, scope_ind: usize, var_name: &str) -> &SymEntry {
        let scope = self.symbol_table.scopes[scope_ind].as_ref();
        match scope.entries.get(var_name) {
            Some(entry) => entry,
            None => {
                eprintln!("Error: variable {} not found in scope {}", var_name, scope_ind);
                panic!();
            }
        }
    }

    // find idx of scope where variable is defined based off the current scope we're in 
    fn get_var_scope_ind(&self, var_name: &str) -> usize {
        let mut search_scope_ind = self.cur_scope_ind;
        // loop through parents scope until we find reference to variable
        loop {
            let cur_scope = self.symbol_table.scopes[search_scope_ind].clone();
            if cur_scope.entries.contains_key(var_name) {
                return search_scope_ind;
            }
            search_scope_ind = match cur_scope.parent_ind {
                Some(parent_ind) => parent_ind,
                None => {
                    eprintln!("Error: variable {} not found in any scope starting at {}", var_name, self.cur_scope_ind);
                    panic!();
                }
            }
        }
    }
}

impl Visitor for SSA_CFG_Compiler {
    fn visit_program(&mut self, program: &AST::Program) {
        // collect global import declarations
        for import_decl in &program.imports {
            self.visit_import_decl(import_decl);
        }
        // collect global field declarations
        for field_decl in &program.fields {
            self.visit_field_decl(field_decl);
        }
        // method declarations
        for method_decl in &program.methods {
            self.visit_method_decl(method_decl);
        }
    }

    fn visit_import_decl(&mut self, import_decl: &AST::ImportDecl) {
        let import_decl_name = import_decl.import_id.name.clone();
        self.imported_funcs.insert(import_decl_name.clone());
        
        // convert import name to byte string and push to globals
        let mut bytes: Vec<i8> = import_decl_name
            .as_bytes()
            .iter()
            .map(|b| *b as i8)
            .collect();
        bytes.push(0);
        self.program_ir.globals.push(GlobalDecl {
            sym: Symbol(import_decl_name.clone()),
            kind: GlobalKind::GlobalStr {
                bytes,
            },
        });
    }
    
    fn visit_field_decl(&mut self, field_decl: &AST::FieldDecl) {
        for var_decl in &field_decl.vars {
            self.visit_var_decl(var_decl);
        }
    }

    fn visit_method_decl(&mut self, _method_decl: &AST::MethodDecl) {
        // Search symbol table for method args and record them
        // create new CFG in FunctionIR
        // create initial basic block
        // visit function block
    }

    fn visit_block(&mut self, _block: &AST::Block) {
        // increment scope to next child scope of parent and add next child scope of the given parent to stack
        // visit all field declarations
        // visit all statements
        // decrement back to parent scope
    }

    fn visit_var_decl(&mut self, var_decl: &AST::VarDecl) { 
        self.visit_identifier(var_decl.name.as_ref());
        let var_name = var_decl.name.name.clone();
        let var_type = self.get_result_var_type();
        let is_global = self.get_is_global();

        // get potential init values
        let mut init_array_len: Option<usize> = None;
        let mut init_array_values: Option<Vec<ConstValue>> = None;
        let mut init_scalar_value: Option<ConstValue> = None;

        if var_decl.is_array {
            // if explicit length given then use that
            if var_decl.array_len.as_ref().as_ref().is_some() {
                let init_array_len_str = var_decl.array_len.as_ref().as_ref().unwrap().value.clone(); 
                init_array_len = Some(init_array_len_str.parse::<i32>().unwrap() as usize);
            } else {
                match var_decl.initializer.as_ref().as_ref().unwrap() {
                    AST::ASTNode::ArrayLiteral(array_literal) => {
                        self.visit_array_literal(array_literal);
                        init_array_values = Some(self.get_array_literal_values());

                        // get array length from initializer values
                        if let Some(values) = init_array_values.as_ref() {
                            init_array_len = Some(values.len());
                        }
                    },
                    _ => {
                        eprintln!("Error: expected array literal for array initializer");
                        panic!();
                    }
                }
            }
        } else {
            if var_decl.initializer.as_ref().as_ref().is_some() {
                self.visit_literal(var_decl.initializer.as_ref().as_ref().unwrap());
                init_scalar_value = Some(self.get_literal_value());
            }
        }
        
        // global variable declaration case
        if is_global {
            match var_type {
                Type::I32 | Type::I64 | Type::I1 => {
                    // get initializeed value if it exists
                    let global_decl = GlobalDecl {
                        sym: Symbol(var_name),
                        kind: GlobalKind::GlobalScalar {
                            ty: var_type,
                            init: init_scalar_value,
                        },
                    };
                    self.program_ir.globals.push(global_decl);
                },
                Type::Ptr(elem_ty) => {
                    let global_decl = GlobalDecl {
                        sym: Symbol(var_name),
                        kind: GlobalKind::GlobalArray {
                            elem_ty: *elem_ty,
                            len: init_array_len.unwrap() as u32,
                            init: init_array_values.clone(),
                        }
                    };
                    self.program_ir.globals.push(global_decl);
                },
                _ => {
                    eprintln!("Error: invalid global variable type");
                    panic!();
                }
            }
        } else {

        }
    }

    fn visit_method_arg_decl(&mut self, _method_arg_decl: &AST::MethodArgDecl) {}

    fn visit_if_statement(&mut self, _if_statement: &AST::IfStatement) {

    }

    fn visit_for_statement(&mut self, _for_statement: &AST::ForStatement) {

    }

    fn visit_while_statement(&mut self, _while_statement: &AST::WhileStatement) {}

    fn visit_return_statement(&mut self, _return_statement: &AST::ReturnStatement) {}

    fn visit_statement_control(&mut self, _statement_control: &AST::StatementControl) {}

    fn visit_assignment(&mut self, _assignment: &AST::Assignment) {}

    fn visit_expression(&mut self, _expr: &AST::ASTNode) {}

    fn visit_method_call(&mut self, _method_call: &AST::MethodCall) {}

    fn visit_len_call(&mut self, _len_call: &AST::LenCall) {}

    fn visit_int_cast(&mut self, _int_cast: &AST::IntCast) {}

    fn visit_long_cast(&mut self, _long_cast: &AST::LongCast) {}

    fn visit_unary_expression(&mut self, _unary_expression: &AST::UnaryExpression) {}

    fn visit_binary_expression(&mut self, _binary_expression: &AST::BinaryExpression) {}

    fn visit_index_expression(&mut self, _index_expression: &AST::IndexExpression) {}

    fn visit_array_literal(&mut self, array_literal: &AST::ArrayLiteral) {
        let mut literal_values: Vec<ConstValue> = vec![];
        for literal in &array_literal.array_values {
            self.visit_literal(literal);
            literal_values.push(self.get_literal_value());
        }
        self.result_array_literal_values = Some(literal_values);
    }

    fn visit_location(&mut self, _location: &AST::ASTNode) {}

    fn visit_literal(&mut self, literal: &AST::ASTNode) {
        match literal {
            AST::ASTNode::IntConstant(int_constant) => {
                self.visit_int_constant(int_constant);
            }
            AST::ASTNode::LongConstant(long_constant) => {
                self.visit_long_constant(long_constant);
            }
            AST::ASTNode::BoolConstant(bool_constant) => {
                self.visit_bool_constant(bool_constant);
            }
            AST::ASTNode::CharConstant(char_constant) => {
                self.visit_char_constant(char_constant);
            }
            _ => {
                eprintln!("Error: invalid literal node");
                panic!();
            }
        }
    }

    fn visit_identifier(&mut self, identifier: &AST::Identifier) {
        let id_name = identifier.name.as_str();

        // get variable scope index in symbol table
        let var_scope_ind = self.get_var_scope_ind(id_name);
        let entry =  self.get_scope_entry(var_scope_ind, id_name);

        // get type of variable being processed
        self.result_var_type = match &entry.get_type() {
            SymType::Int => Type::I32,
            SymType::Long => Type::I64,
            SymType::Bool => Type::I1,
            SymType::Void => Type::Void,
            SymType::IntArray => Type::Ptr(Box::new(Type::I32)),
            SymType::LongArray => Type::Ptr(Box::new(Type::I64)),
            SymType::BoolArray => Type::Ptr(Box::new(Type::I1)),
            SymType::None => {
                eprintln!("Error: variable {} has invalid type None", id_name);
                panic!();
            }
        }; 

        let is_global = var_scope_ind == 0;
        self.result_is_global = Some(is_global);

        match identifier.status {
            // if we're creating new variable in scope we should assign it a new value id
            0 | 2 => {
                if !is_global {
                    let new_value_id = self.get_cur_value_id();
                    self.var_to_value_id
                        .entry(var_scope_ind)
                        .or_insert(HashMap::new())
                        .insert(id_name.to_string(), new_value_id); // placeholder value id
                }
            },
            1 => (),
            _ => {
                eprintln!("Error: invalid identifier status must be one of (0, 1, 2)");
            }
        }
    }

    fn visit_int_constant(&mut self, int_constant: &AST::IntConstant) {
        let int_value: i32;
        if int_constant.value.contains("x") {
            let int_constant_str: String;
            if int_constant.is_neg {
                int_constant_str = format!("-{}", &int_constant.value[2..]);
            } else {
                int_constant_str = int_constant.value[2..].to_string();
            }
            int_value = i32::from_str_radix(int_constant_str.as_str(), 16).unwrap();
        } else {
            int_value = int_constant.value.parse::<i32>().unwrap();
        }
        self.result_literal_value = Some(ConstValue::I32(int_value));
    }

    fn visit_long_constant(&mut self, long_constant: &AST::LongConstant) {
        let long_value: i64;
        if long_constant.value.contains("x") {
            let long_constant_str: String;
            if long_constant.is_neg {
                long_constant_str = format!("-{}", &long_constant.value[2..]);
            } else {
                long_constant_str = long_constant.value[2..].to_string();
            }
            long_value = i64::from_str_radix(long_constant_str.as_str(), 16).unwrap();
        } else {
            long_value = long_constant.value.parse::<i64>().unwrap();
        }
        self.result_literal_value = Some(ConstValue::I64(long_value));
    }

    fn visit_string_constant(&mut self, _string_constant: &AST::StringConstant) {}

    fn visit_bool_constant(&mut self, bool_constant: &AST::BoolConstant) {
        self.result_literal_value = Some(ConstValue::I1(bool_constant.value));
    }

    fn visit_char_constant(&mut self, char_constant: &AST::CharConstant) {
        let raw = char_constant.value.as_str();
        let ch = if raw.len() == 1 {
            raw.chars().next().unwrap()
        } else if raw.len() == 2 && raw.starts_with('\\') {
            match raw.chars().nth(1).unwrap() {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '\\' => '\\',
                '\'' => '\'',
                '\"' => '\"',
                other => {
                    eprintln!("Error: invalid char escape: \\{}", other);
                    panic!();
                }
            }
        } else {
            eprintln!("Error: invalid char literal: {}", raw);
            panic!();
        };

        self.result_literal_value = Some(ConstValue::I32(ch as i32));
    }   
}

pub fn compile_to_ssa_cfg(ast: AST::Program, symbol_table: SymbolTable) -> ProgramIR {
    let mut ssa_cfg_compiler = SSA_CFG_Compiler {
        program_ir: ProgramIR {
            globals: vec![],
            functions: HashMap::new(), 
        },
        cur_value_id: 0,
        cur_block_id: 0,
        cur_mem_id: 0,
        cur_scope_ind: 0,
        cur_child_scope_map: HashMap::new(),
        var_to_value_id: HashMap::new(),
        symbol_table: symbol_table,
        imported_funcs: HashSet::new(),
        result_var_type: Type::None,
        result_is_global: None,
        result_literal_value: None,
        result_array_literal_values: None,
    };
    ssa_cfg_compiler.visit_program(&ast);
    return ssa_cfg_compiler.program_ir;
}
