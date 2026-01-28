use super::super::parser::visitor::{Visitor};
use super::super::semantics::symbol_table::{SymbolTable, Entry as SemEntry, Type as SemType};
use super::super::parser::AST;
use super::three_address_code::{ProgramIR, Symbol, GlobalDecl, GlobalKind, Type, ConstValue};
use std::collections::{HashSet, HashMap};

#[allow(non_camel_case_types)]
pub struct SSA_CFG_Compiler {
    // final output IR
    program_ir: ProgramIR,

    // variable/func tracking
    globals_map: HashMap<String, GlobalKind>,
    imported_funcs: HashSet<String>,
    var_to_value_id: HashMap<String, usize>, // latest var number associated with a variable in AST

    // tracking state (globally)
    cur_value_id: u32,
    cur_block_id: u32,
    cur_mem_id: u32,
    cur_scope_idx: usize,
    symbol_table: SymbolTable,
    is_global: bool,
    
    // tracking state (per-scope)
    cur_child_scope_map: HashMap<usize, usize> // map from parent scope idx to which child scope idx we're on
}

impl SSA_CFG_Compiler {
    fn string_to_type(&self, type_name: &str, is_array: bool) -> Type {
        let mut var_type = match type_name {
            "int" => Type::I32,
            "long" => Type::I64,
            "bool" => Type::I1,
            "void" => Type::Void,
            _ => Type::Void,
        };
        if is_array {
            var_type = Type::Ptr(Box::new(var_type));
        }
        return var_type;
    }
}

impl Visitor for SSA_CFG_Compiler {
    fn visit_program(&mut self, _program: &AST::Program) {
        self.is_global = true;
        // collect global import declarations
        for import_decl in &_program.imports {
            self.visit_import_decl(import_decl);
        }
        // collect global field declarations
        for field_decl in &_program.fields {
            self.visit_field_decl(field_decl);
        }
        self.is_global = false;
        // method declarations
        for method_decl in &_program.methods {
            self.visit_method_decl(method_decl);
        }
    }

    fn visit_import_decl(&mut self, _import_decl: &AST::ImportDecl) {
        let import_decl_name = _import_decl.import_id.name.clone();
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
    
    fn visit_field_decl(&mut self, _field_decl: &AST::FieldDecl) {
        for var_decl in &_field_decl.vars {
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

    fn visit_var_decl(&mut self, _var_decl: &AST::VarDecl) {}

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

    fn visit_array_literal(&mut self, _array_literal: &AST::ArrayLiteral) {}

    fn visit_location(&mut self, _location: &AST::ASTNode) {}

    fn visit_literal(&mut self, _literal: &AST::ASTNode) {}

    fn visit_identifier(&mut self, _identifier: &AST::Identifier) {}

    fn visit_int_constant(&mut self, _int_constant: &AST::IntConstant) {}

    fn visit_long_constant(&mut self, _long_constant: &AST::LongConstant) {}

    fn visit_string_constant(&mut self, _string_constant: &AST::StringConstant) {}

    fn visit_bool_constant(&mut self, _bool_constant: &AST::BoolConstant) {}

    fn visit_char_constant(&mut self, _char_constant: &AST::CharConstant) {}   
}

pub fn compile_to_ssa_cfg(ast: AST::Program, symbol_table: SymbolTable) -> ProgramIR {
    let mut ssa_cfg_compiler = SSA_CFG_Compiler {
        program_ir: ProgramIR {
            globals: vec![],
            functions: HashMap::new(), 
        },
        globals_map: HashMap::new(),
        cur_value_id: 0,
        cur_block_id: 0,
        cur_mem_id: 0,
        cur_scope_idx: 0,
        cur_child_scope_map: HashMap::new(),
        var_to_value_id: HashMap::new(),
        symbol_table: symbol_table,
        imported_funcs: HashSet::new(),
        is_global: false,
    };
    ssa_cfg_compiler.visit_program(&ast);
    return ssa_cfg_compiler.program_ir;
}
