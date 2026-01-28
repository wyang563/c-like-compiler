use super::super::parser::parser::parse_file;
use super::super::parser::visitor::Visitor;
use super::super::parser::AST;
use super::symbol_table::{
    ArrayEntry, Entry, ImportEntry, MethodEntry, SymbolTable, Table, Type, VarEntry,
};

use core::panic;
use std::collections::HashMap;

pub struct Interpreter {
    scopes: Vec<Box<Table>>, // vec of scopes which scope graph will reference by index
    vars: Vec<Box<Entry>>,
    errors: Vec<String>,
    correct: bool,

    // func parameters + flags
    checking_type: bool, // whether we are checking the type of a variable, used during field declarations
    init_method: bool, // whether we are initializing a method, this is so we don't create two scopes when we do visit method_decl and then visit_block
    init_type: Type,   // type of varaible being initialized
    in_loop: u32, // we use ints here instead of bool flags since if we have layered loops or expressions we don't want to set this to false once we finish an inner loop/expression
    in_expr: u32,
    in_location: bool,
    var_count: usize,
    cur_scope_ind: usize,

    // func result holders
    result_expr_type: Type,

    // debug mode
    debug: bool,
}

impl Interpreter {
    // find whether variable has been declared
    fn find_var(&mut self, var_name: &str) -> Result<Entry, ()> {
        // Rule 2: No identifier is used before it is declared
        // Rule 12: An ⟨id⟩ used as a ⟨location⟩ must name a declared local/global variable or parameter.

        // loop through scopes in reverse and check for value
        let mut search_scope_ind = self.cur_scope_ind;
        loop {
            let cur_scope = self.scopes[search_scope_ind].as_ref();
            if cur_scope.entries.contains_key(var_name) {
                return Ok(cur_scope.entries[var_name].clone());
            }
            search_scope_ind = match cur_scope.parent_ind {
                Some(parent_ind) => parent_ind,
                None => break,
            };
        }

        self.push_error(&format!(
            "Error: Identifier {} is used before it is declared.",
            var_name
        ));
        return Err(());
    }

    fn check_declared(&mut self, var_name: &str) -> bool {
        // Rule 1: No identifier is declared twice in the same scope
        let cur_scope = self.scopes[self.cur_scope_ind].as_ref();
        if cur_scope.entries.contains_key(var_name) {
            self.push_error(&format!(
                "Error: Identifier {} is declared twice in the same scope.",
                var_name
            ));
            return true;
        }
        return false;
    }

    fn write_to_table(&mut self, var_name: &str, entry: Entry) {
        let cur_scope = self.scopes[self.cur_scope_ind].as_mut();
        cur_scope.entries.insert(var_name.to_string(), entry);
    }

    fn incr_var_count(&mut self) -> usize {
        self.var_count += 1;
        return self.var_count - 1;
    }

    fn string_to_type(&mut self, str_type: &str) -> Type {
        match str_type {
            "int" => Type::Int,
            "long" => Type::Long,
            "bool" => Type::Bool,
            "void" => Type::Void,
            _ => panic!("invalid type"),
        }
    }

    fn extract_method_arg_var(&mut self, arg: &AST::MethodArgDecl) -> VarEntry {
        let arg_name = arg.name.as_ref().name.as_str();
        let arg_type = self.string_to_type(arg.type_name.as_str());
        let var_entry = VarEntry {
            name: arg_name.to_string(),
            var_type: arg_type.clone(),
            is_const: false,
            scope: self.cur_scope_ind,
            id: self.incr_var_count(),
        };
        self.vars.push(Box::new(Entry::Var(var_entry.clone())));
        return var_entry;
    }

    fn push_error(&mut self, error: &str) {
        self.errors.push(error.to_string());
        self.correct = false;
    }

    // debugging helpers
    #[allow(dead_code)]
    fn print_scope(&mut self) {
        if self.debug {
            for (key, value) in &self.scopes[self.cur_scope_ind].entries {
                println!("{}: {:?}", key, value);
            }
        }
    }

    #[allow(dead_code)]
    fn debug_print(&mut self, print_str: &str) {
        if self.debug {
            println!("{}", print_str);
        }
    }
}

impl Visitor for Interpreter {
    fn visit_program(&mut self, program: &AST::Program) {
        for import_decl in &program.imports {
            self.visit_import_decl(import_decl);
        }
        for field_decl in &program.fields {
            self.visit_field_decl(field_decl);
        }
        for method_decl in &program.methods {
            self.visit_method_decl(method_decl);
        }
        // Rule 3: The program contains a definition for a method called main that has type void and takes no parameters.
        let global_scope = self.scopes[0].as_ref();
        if global_scope.entries.contains_key("main") {
            match global_scope.entries.get("main").unwrap() {
                Entry::Method(main_entry) => {
                    if main_entry.name != "main" || main_entry.return_type != Type::Void || main_entry.param_count != 0 {
                        self.push_error("Error: The program does not contain a definition for a method called main that has type void and takes no parameters.");
                    }
                },
                _ => self.push_error("Error: The program does not contain a definition for a method called main that has type void and takes no parameters."),
            }
        } else {
            self.push_error("Error: The program does not contain a definition for a method called main that has type void and takes no parameters.");
        }
    }

    fn visit_import_decl(&mut self, import_decl: &AST::ImportDecl) {
        let import_id = import_decl.import_id.name.clone();
        // Rule 1: No identifier is declared twice in the same scope
        if self.check_declared(import_id.as_str()) {
            return;
        }
        let import_entry = ImportEntry {
            name: import_id.clone(),
            return_type: Type::Int,
            is_const: false,
            scope: self.cur_scope_ind,
            id: self.incr_var_count(),
        };
        self.vars
            .push(Box::new(Entry::Import(import_entry.clone())));
        self.write_to_table(import_id.as_str(), Entry::Import(import_entry));
    }

    fn visit_field_decl(&mut self, field_decl: &AST::FieldDecl) {
        for var_decl in &field_decl.vars {
            self.visit_var_decl(var_decl);
        }
    }

    fn visit_method_decl(&mut self, method_decl: &AST::MethodDecl) {
        self.init_method = true;

        // Rule 1: No identifier is declared twice in the same scope
        self.visit_identifier(&method_decl.name);

        let method_type = self.string_to_type(method_decl.type_name.as_str());
        let method_name_str = method_decl.name.name.as_str();
        // write function to global scope
        let mut method_entry = MethodEntry {
            name: method_name_str.to_string(),
            return_type: method_type.clone(),
            is_const: false,
            param_list: vec![],
            param_count: method_decl.args.len(),
            scope: self.cur_scope_ind,
            id: 0,
        };

        for arg in &method_decl.args {
            method_entry
                .param_list
                .push(self.extract_method_arg_var(arg.as_ref()));
        }
        method_entry.id = self.incr_var_count();
        self.vars
            .push(Box::new(Entry::Method(method_entry.clone())));

        self.write_to_table(method_decl.name.name.as_str(), Entry::Method(method_entry));

        // create new scope
        let method_table = Table {
            entries: HashMap::new(),
            method_return_type: method_type.clone(),
            scope_ind: self.scopes.len(),
            parent_ind: Some(self.cur_scope_ind),
            children_inds: vec![],
        };

        self.scopes.push(Box::new(method_table));

        // add children to parent
        self.cur_scope_ind = self.scopes.len() - 1;
        let parent_ind = self.scopes[self.cur_scope_ind].parent_ind.unwrap();
        self.scopes[parent_ind]
            .children_inds
            .push(self.cur_scope_ind);

        // add method args to scope
        for arg in &method_decl.args {
            self.visit_method_arg_decl(arg.as_ref());
        }
        self.visit_block(&method_decl.body);
    }

    fn visit_block(&mut self, block: &AST::Block) {
        if !self.init_method {
            let cur_scope = self.scopes[self.cur_scope_ind].as_ref();
            let block_table = Table {
                entries: HashMap::new(),
                method_return_type: cur_scope.method_return_type.clone(),
                scope_ind: self.scopes.len(),
                parent_ind: Some(self.cur_scope_ind),
                children_inds: vec![],
            };
            self.scopes.push(Box::new(block_table));

            // add children to parent inds childs array
            self.cur_scope_ind = self.scopes.len() - 1;
            let parent_ind = self.scopes[self.cur_scope_ind].parent_ind.unwrap();
            self.scopes[parent_ind]
                .children_inds
                .push(self.cur_scope_ind);
        }
        self.init_method = false;

        for field_decl in &block.fields {
            self.visit_field_decl(field_decl);
        }

        for statement in &block.statements {
            statement.accept(self);
        }
        // exit out of lowest scope
        self.cur_scope_ind = self.scopes[self.cur_scope_ind].parent_ind.unwrap();
    }

    fn visit_var_decl(&mut self, var_decl: &AST::VarDecl) {
        self.init_type = self.string_to_type(var_decl.type_name.as_str());
        let var_name = var_decl.name.as_ref().name.as_str();

        // Rule 1: No identifier is declared twice in the same scope
        self.visit_identifier(var_decl.name.as_ref());

        // Rule 22: Declarations of const locations must have an initializer
        if var_decl.is_const && var_decl.initializer.as_ref().is_none() {
            self.push_error(&format!(
                "Error: Const location {} must have an initializer.",
                var_decl.name.as_ref().name
            ));
            return;
        }

        if var_decl.is_array {
            if let Some(array_len_node) = var_decl.array_len.as_ref() {
                self.visit_int_constant(array_len_node);
                // Rule 6: If present, the ⟨int literal⟩ in an array declaration must be greater than 0.
                if array_len_node.value.parse::<i32>().unwrap() <= 0 {
                    self.push_error(&format!(
                        "Error: Array initializer length must be greater than 0."
                    ));
                }
                // Rule 5: Array initializers have either a declared length or an initializer list, but not both.
                if var_decl.initializer.as_ref().as_ref().is_some() {
                    self.push_error(&format!("Error: Array initializers have either a declared length or an initializer list, but not both."));
                }
            } else {
                // Rule 5: Array initializers have either a declared length or an initializer list, but not both.
                if var_decl.initializer.as_ref().as_ref().is_none() {
                    self.push_error(&format!("Error: Array initializers have either a declared length or an initializer list, but not both."));
                }

                match var_decl.initializer.as_ref().as_ref().unwrap() {
                    AST::ASTNode::ArrayLiteral(array_literal) => {
                        self.visit_array_literal(array_literal);
                    }
                    _ => {
                        self.push_error(&format!("Error: expected an array list as initializer for variable of type array."));
                    }
                }
            }
            // add to symbol table
            let array_type = match self.init_type {
                Type::Int => Type::IntArray,
                Type::Bool => Type::BoolArray,
                Type::Long => Type::LongArray,
                _ => panic!("invalid type"),
            };

            let var_id = self.incr_var_count();
            let array_entry = ArrayEntry {
                name: var_name.to_string(),
                var_type: array_type,
                is_const: var_decl.is_const,
                scope: self.cur_scope_ind,
                id: var_id,
            };
            self.vars.push(Box::new(Entry::Array(array_entry.clone())));
            self.write_to_table(var_name, Entry::Array(array_entry));
        } else {
            if var_decl.initializer.as_ref().as_ref().is_some() {
                self.visit_literal(var_decl.initializer.as_ref().as_ref().unwrap());
            }

            let var_id = self.incr_var_count();
            let var_entry = VarEntry {
                name: var_name.to_string(),
                var_type: self.init_type.clone(),
                is_const: var_decl.is_const,
                scope: self.cur_scope_ind,
                id: var_id,
            };
            self.vars.push(Box::new(Entry::Var(var_entry.clone())));
            self.write_to_table(var_name, Entry::Var(var_entry));
        }
    }

    fn visit_method_arg_decl(&mut self, method_arg_decl: &AST::MethodArgDecl) {
        // Rule 1: No identifier is declared twice in the same scope
        self.visit_identifier(method_arg_decl.name.as_ref());

        let method_entry = self.extract_method_arg_var(method_arg_decl);
        let arg_name = method_arg_decl.name.as_ref().name.as_str();
        self.write_to_table(arg_name, Entry::Var(method_entry));
    }

    fn visit_if_statement(&mut self, if_statement: &AST::IfStatement) {
        // Rule 16: The ⟨expr⟩ in an if or while statement must have type bool , as well as the second ⟨expr⟩ of a for statement.
        self.visit_expression(if_statement.condition.as_ref());
        if self.result_expr_type != Type::Bool {
            self.push_error("Error: The expression in an if statement must have type bool.");
        }
        self.visit_block(if_statement.then_block.as_ref());
        if let Some(else_block) = if_statement.else_block.as_ref() {
            self.visit_block(else_block);
        }
    }

    fn visit_for_statement(&mut self, for_statement: &AST::ForStatement) {
        let incr_var = for_statement.start_assignment.assign_var.as_ref();
        self.visit_location(incr_var);

        // Visit initial incr var assignment to check validity
        self.visit_assignment(&for_statement.start_assignment);

        // Rule 16: The ⟨expr⟩ in an if or while statement must have type bool , as well as the second ⟨expr⟩ of a for statement.
        self.visit_expression(&for_statement.end_expr);
        if self.result_expr_type != Type::Bool {
            self.push_error(
                "Error: The ending condition expression in a for statement must have type bool.",
            );
        }
        // Visit update expression to check validity
        match for_statement.update_expr.as_ref() {
            AST::ASTNode::MethodCall(method_call) => {
                self.visit_method_call(method_call);
            }
            AST::ASTNode::Assignment(assignment) => {
                self.visit_assignment(assignment);
            }
            _ => self.push_error("Error: invalid update expression in for statement."),
        }

        self.in_loop += 1;
        self.visit_block(for_statement.block.as_ref());
        self.in_loop -= 1;
    }

    fn visit_while_statement(&mut self, while_statement: &AST::WhileStatement) {
        // Rule 16: The ⟨expr⟩ in an if or while statement must have type bool , as well as the second ⟨expr⟩ of a for statement.
        self.visit_expression(&while_statement.condition);
        if self.result_expr_type != Type::Bool {
            self.push_error("Error: The expression in a while statement must have type bool.");
        }
        self.in_loop += 1;
        self.visit_block(&while_statement.block);
        self.in_loop -= 1;
    }

    fn visit_return_statement(&mut self, return_statement: &AST::ReturnStatement) {
        // Rule 10: A return statement must not have a return value unless it appears in the body of a method that is declared to return a value
        if self.cur_scope_ind == 0 {
            self.push_error("Error: A return statement must appear in a method body definition, not the global scope.");
        }
        let method_return_type = self.scopes[self.cur_scope_ind].method_return_type.clone();

        if method_return_type == Type::Void {
            if return_statement.expr.is_some() {
                self.push_error("Error: A return statement must not have a return value unless it appears in the body of a method that is declared to return a value.");
            }
        } else {
            if return_statement.expr.is_none() {
                self.push_error("Error: A return statement must have a return expression in the body of a method that is declared to return a value.");
            } else {
                self.visit_expression(return_statement.expr.as_ref().as_ref().unwrap());
                // Rule 11: The expression in a return statement must have the same type as the declared result type of the enclosing method definition.
                if self.result_expr_type != method_return_type {
                    self.push_error(&format!("Error: The expression in a return statement must have the same type as the declared result type of the enclosing method definition."));
                }
            }
        }
    }

    fn visit_statement_control(&mut self, _statement_control: &AST::StatementControl) {
        // Rule 24: All break and continue statements must be contained within the body of a for or a while statement.
        if self.in_loop <= 0 {
            self.push_error("Error: All break and continue statements must be contained within the body of a for or a while statement.");
        }
    }

    fn visit_assignment(&mut self, assignment: &AST::Assignment) {
        // Rule 20: The ⟨location⟩ and the ⟨expr⟩ in an assignment, ⟨location⟩ = ⟨expr⟩, must have the same type.
        self.visit_location(assignment.assign_var.as_ref());
        let lhs_type = self.result_expr_type.clone();
        if assignment.expr.is_some() {
            let rhs_expr = assignment.expr.as_ref().as_ref().unwrap();
            self.visit_expression(rhs_expr);
            let rhs_type = self.result_expr_type.clone();
            if lhs_type != rhs_type {
                self.push_error(&format!(
                    "Error: The location and expression in an assignment must have the same type."
                ));
            }

            // Rule 21: The⟨location⟩ and the ⟨expr⟩ in a compound assignment,⟨location⟩+=⟨expr⟩,⟨location⟩-=⟨expr⟩, ⟨location⟩ *= ⟨expr⟩, ⟨location⟩ /= ⟨expr⟩, and ⟨location⟩ %= ⟨expr⟩, must be of type int . The same is true of the ⟨location⟩ in ++ and -- statements.
            match assignment.assign_op.as_str() {
                "=" => (),
                "+=" | "-=" | "*=" | "/=" | "%=" => {
                    if ![Type::Int, Type::Long].contains(&lhs_type) {
                        self.push_error(&format!("Error: The location and expression in an assignment must have type int or long in compound expression {}.", assignment.assign_op.as_str()));
                    }
                }
                _ => self.push_error(&format!("Error: invalid assignment operator found.")),
            }
        } else {
            // case we have ++, -- operation
            if ![Type::Int, Type::Long].contains(&lhs_type) {
                self.push_error(&format!("Error: The location in an increment or decrement assignment expression must have type int or long."));
            }
        }
    }

    fn visit_method_call(&mut self, method_call: &AST::MethodCall) {
        // Rule 13: The ⟨id⟩ in a method statement must be a declared method or import.
        let method_name = method_call.name.name.as_str();
        match self.find_var(method_name) {
            Ok(result_entry) => {
                match result_entry {
                    Entry::Method(method_entry) => {
                        // Rule 8: If a method call is used as an expression, the method must return a result.
                        if self.in_expr > 0 {
                            if self.result_expr_type == Type::Void {
                                self.push_error(&format!("Error: Method {} used in an expression must return a non-void value", method_name));
                            }
                        }
                        // Rule 7: The number and types of parameters in a method call (non-import) must be the same as the number and types of the declared parameters for the method.
                        if method_entry.param_count != method_call.args.len() {
                            self.push_error(&format!("Error: Method call to {} has incorrect number of parameters as: expected {} but got {}", method_name, method_entry.param_count, method_call.args.len()));
                            return;
                        }

                        // Rule 7: The number and types of parameters in a method call (non-import) must be the same as the number and types of the declared parameters for the method.
                        // Rule 9: String literals and array variables may not be used as parameters to non-import methods.
                        for (i, arg_expr) in method_call.args.iter().enumerate() {
                            self.visit_expression(arg_expr.as_ref());
                            let expected_type = method_entry.param_list[i].var_type.clone();
                            if self.result_expr_type != expected_type {
                                self.push_error(&format!("Error: expected parameter {} in method call {} to have type {:?} but found type {:?}", i, method_name, expected_type, self.result_expr_type));
                            }
                            if [Type::IntArray, Type::LongArray, Type::BoolArray]
                                .contains(&self.result_expr_type)
                            {
                                self.push_error(&format!("Error: Array variables may not be used as parameters to non-import methods."));
                            }
                        }
                        self.result_expr_type = method_entry.return_type;
                    }
                    Entry::Import(_) => {
                        for arg_expr in method_call.args.iter() {
                            self.visit_expression(arg_expr.as_ref());
                        }
                        self.result_expr_type = Type::Int;
                    }
                    _ => self.push_error(&format!(
                        "Error: Identifier {} is not a declared method or import.",
                        method_name
                    )),
                }
            }
            Err(()) => {
                self.result_expr_type = Type::None;
                return;
            }
        }
    }

    fn visit_len_call(&mut self, len_call: &AST::LenCall) {
        let var_name = len_call.id.name.as_str();
        // Rule 15: The argument of the len operator must be an array variable.
        match self.find_var(var_name) {
            Ok(id_entry) => match id_entry {
                Entry::Array(_) => (),
                _ => self.push_error(&format!(
                    "Error: Argument of len operator must be an array variable."
                )),
            },
            Err(()) => (),
        }
        self.result_expr_type = Type::Int;
    }

    fn visit_int_cast(&mut self, int_cast: &AST::IntCast) {
        self.visit_expression(int_cast.cast_expr.as_ref());
        if ![Type::Long, Type::Int].contains(&self.result_expr_type) {
            self.push_error("Error: The expression in an int cast must have type int or long.");
        }
        self.result_expr_type = Type::Int;
    }

    fn visit_long_cast(&mut self, long_cast: &AST::LongCast) {
        self.visit_expression(long_cast.cast_expr.as_ref());
        if ![Type::Long, Type::Int].contains(&self.result_expr_type) {
            self.push_error("Error: The expression in an long cast must have type int or long.");
        }
        self.result_expr_type = Type::Long;
    }

    fn visit_unary_expression(&mut self, unary_expression: &AST::UnaryExpression) {
        // Rule 17: The operands of the unary minus, ⟨arith op⟩s and ⟨rel op⟩s must have type int
        // Rule 19: The operands of ⟨cond op⟩s and the operand of logical not ( ! ) must have type bool
        match unary_expression.op.as_str() {
            "!" => {
                self.visit_expression(unary_expression.expr.as_ref());
                if self.result_expr_type != Type::Bool {
                    self.push_error("Error: The operand of logical not ( ! ) must have type bool.");
                }
                self.result_expr_type = Type::Bool;
            }
            "-" => {
                self.visit_expression(unary_expression.expr.as_ref());
                if ![Type::Int, Type::Long].contains(&self.result_expr_type) {
                    self.push_error(
                        "Error: The operand of unary minus must have type int or long.",
                    );
                }
                self.result_expr_type = self.result_expr_type.clone();
            }
            _ => {
                self.push_error(&format!(
                    "Error: invalid unary operator {} found.",
                    unary_expression.op
                ));
                self.result_expr_type = Type::None;
            }
        }
    }

    fn visit_binary_expression(&mut self, binary_expression: &AST::BinaryExpression) {
        // Rule 17: The operands of the unary minus, ⟨arith op⟩s and ⟨rel op⟩s must have type int
        // Rule 18: The operands of ⟨eq op⟩s must have the same type, either int or bool
        // Rule 19: The operands of ⟨cond op⟩s and the operand of logical not ( ! ) must have type bool
        self.visit_expression(binary_expression.left_expr.as_ref());
        let left_type = self.result_expr_type.clone();
        self.visit_expression(binary_expression.right_expr.as_ref());
        let right_type = self.result_expr_type.clone();
        match binary_expression.op.as_str() {
            "+" | "-" | "*" | "/" | "%" => {
                if ![Type::Int, Type::Long].contains(&left_type) {
                    self.push_error(&format!("Error: The operands of the arithmetic operator {} must have type int or long.", binary_expression.op));
                }
                if left_type != right_type {
                    self.push_error(&format!("Error: The type of the operands of the arithmetic operator {} must be the same.", binary_expression.op));
                }
                self.result_expr_type = left_type.clone();
            }
            "<" | "<=" | ">" | ">=" => {
                if ![Type::Int, Type::Long].contains(&left_type) {
                    self.push_error(&format!("Error: The operands of the comparison operator {} must have type int or long.", binary_expression.op));
                }
                if left_type != right_type {
                    self.push_error(&format!("Error: The type of the operands of the comparison operator {} must be the same.", binary_expression.op));
                }
                self.result_expr_type = Type::Bool;
            }
            "==" | "!=" => {
                if left_type != right_type {
                    self.push_error(&format!(
                        "Error: The operands of the equality operator {} must have the same type.",
                        binary_expression.op
                    ));
                }
                self.result_expr_type = Type::Bool;
            }
            "&&" | "||" => {
                if left_type != Type::Bool || right_type != Type::Bool {
                    self.push_error(&format!(
                        "Error: The operands of the conditional operator {} must have type bool.",
                        binary_expression.op
                    ));
                }
                self.result_expr_type = Type::Bool;
            }
            _ => {
                self.push_error(&format!(
                    "Error: invalid binary operator {} found.",
                    binary_expression.op
                ));
                self.result_expr_type = Type::None;
            }
        }
    }

    fn visit_index_expression(&mut self, index_expression: &AST::IndexExpression) {
        // Rule 14: For all locations of the form ⟨id⟩[⟨expr⟩], the ⟨id⟩ must be an array variable and the type of ⟨expr⟩ must be int.
        if let Ok(array_entry) = self.find_var(index_expression.id.name.as_str()) {
            match array_entry {
                Entry::Array(_) => {
                    self.visit_identifier(index_expression.id.as_ref());
                    self.visit_expression(index_expression.idx_expr.as_ref());
                    if self.result_expr_type != Type::Int {
                        self.push_error(&format!(
                            "Error: Index expression for array access to {} must have type int.",
                            index_expression.id.name.as_str()
                        ));
                    }
                    match array_entry.get_type() {
                        Type::IntArray => self.result_expr_type = Type::Int,
                        Type::LongArray => self.result_expr_type = Type::Long,
                        Type::BoolArray => self.result_expr_type = Type::Bool,
                        _ => self.result_expr_type = Type::None,
                    }
                }
                _ => self.push_error(&format!(
                    "Error: Identifier {} must be an array variable.",
                    index_expression.id.name.as_str()
                )),
            }
        } else {
            self.result_expr_type = Type::None;
        }
    }

    fn visit_expression(&mut self, expression: &AST::ASTNode) {
        self.in_expr += 1;
        match expression {
            AST::ASTNode::UnaryExpression(unary_expression) => {
                self.visit_unary_expression(unary_expression);
            }
            AST::ASTNode::BinaryExpression(binary_expression) => {
                self.visit_binary_expression(binary_expression);
            }
            AST::ASTNode::LenCall(len_call) => {
                self.visit_len_call(len_call);
            }
            AST::ASTNode::IntCast(int_cast) => {
                self.visit_int_cast(int_cast);
            }
            AST::ASTNode::LongCast(long_cast) => {
                self.visit_long_cast(long_cast);
            }
            AST::ASTNode::MethodCall(method_call) => {
                self.visit_method_call(method_call);
            }
            AST::ASTNode::IndexExpression(index_expression) => {
                self.visit_index_expression(index_expression);
            }
            AST::ASTNode::Identifier(identifier) => {
                self.visit_identifier(identifier);
            }
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
            AST::ASTNode::StringConstant(str_constant) => {
                self.visit_string_constant(str_constant);
            }
            _ => {
                self.push_error("Error: invalid expression type found (check grammar).");
            }
        }
        self.in_expr -= 1;
    }

    fn visit_array_literal(&mut self, array_literal: &AST::ArrayLiteral) {
        for literal in &array_literal.array_values {
            self.visit_literal(literal);
        }
    }

    fn visit_literal(&mut self, literal: &AST::ASTNode) {
        self.checking_type = true;
        // Rule 4: All types of initializers must match the type of the variable being initialized.
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
                self.push_error("Error: invalid type for literal - expected either int or bool.");
            }
        }
        self.checking_type = false;
    }

    fn visit_location(&mut self, location: &AST::ASTNode) {
        self.in_location = true;
        match location {
            AST::ASTNode::Identifier(identifier) => {
                // Rule 10: An <id> used as a <location> must name a declared local/global variable or formal parameter.
                self.visit_identifier(identifier);
            }
            AST::ASTNode::IndexExpression(index_expression) => {
                // Rule 10: An <id> used as a <location> must name a declared local/global variable or formal parameter.

                self.visit_index_expression(index_expression);
            }
            _ => {
                self.push_error("Error: invalid location type found (check grammar).");
                self.result_expr_type = Type::None;
            }
        }
        self.in_location = false;
    }

    fn visit_identifier(&mut self, identifier: &AST::Identifier) {
        let id_name = identifier.name.as_str();
        match identifier.status {
            // init variable
            0 => {
                // Rule 1: No identifier is declared twice in the same scope
                self.check_declared(id_name);
            }
            // read variable
            1 => {
                // Rule 2: No identifier is used before it is declared
                match self.find_var(id_name) {
                    Ok(id_entry) => {
                        self.result_expr_type = id_entry.get_type();
                    }
                    Err(()) => {
                        self.result_expr_type = Type::None;
                    }
                }
            }
            // write variable
            2 => {
                // Rule 2: No identifier is used before it is declared
                match self.find_var(id_name) {
                    Ok(id_entry) => {
                        // Rule 23: const locations may not be assigned to
                        if id_entry.get_is_const() {
                            self.push_error(&format!("Error: Identifier {} is a const location and may not be assigned to.", id_name));
                        }
                        self.result_expr_type = id_entry.get_type();
                        // Rule 10: An <id> used as a <location> must name a declared local/global variable or formal parameter.
                        if self.in_location {
                            match id_entry {
                                Entry::Method(_) => {
                                    self.push_error(&format!("Error: Id {} used as a location must have a declared local/global variable or formal parameter", id_name));
                                }
                                Entry::Import(_) => {
                                    self.push_error(&format!("Error: Id {} used as a location must have a declared local/global variable or formal parameter", id_name));
                                }
                                _ => (),
                            }
                        }
                    }
                    Err(()) => {
                        self.result_expr_type = Type::None;
                    }
                }
            }
            _ => {
                self.push_error(&format!(
                    "Error: Identifier status {} is invalid: not one of 0, 1, 2.",
                    identifier.status
                ));
                self.result_expr_type = Type::None;
            }
        }
    }

    fn visit_int_constant(&mut self, int_constant: &AST::IntConstant) {
        // Rule 25: All integer literals must be in the 64 bit integer range: −9223372036854775808 ≤ x ≤ 9223372036854775807
        // hex numbers
        if int_constant.value.contains("x") {
            let int_constant_str: String;
            if int_constant.is_neg {
                int_constant_str = format!("-{}", &int_constant.value[2..]);
            } else {
                int_constant_str = int_constant.value[2..].to_string();
            }
            match i32::from_str_radix(int_constant_str.as_str(), 16) {
                Ok(_) => (),
                Err(_) => {
                    self.push_error(&format!(
                        "Error: Integer literal {} is out of 32 bit range.",
                        int_constant.value
                    ));
                }
            }
        } else {
            let mut int_constant_str = int_constant.value.clone();
            if int_constant.is_neg {
                int_constant_str = format!("-{}", int_constant_str);
            }
            match int_constant_str.as_str().parse::<i32>() {
                Ok(_) => (),
                Err(_) => {
                    self.push_error(&format!(
                        "Error: Integer literal {} is out of 32 bit range.",
                        int_constant.value
                    ));
                }
            }
        }
        if self.checking_type {
            if self.init_type != Type::Int {
                self.push_error(&format!(
                    "Error: expected {:?} as type for initializer variable not int",
                    self.init_type
                ));
                self.result_expr_type = self.init_type.clone();
                return;
            }
        }
        self.result_expr_type = Type::Int;
    }

    fn visit_long_constant(&mut self, long_constant: &AST::LongConstant) {
        if long_constant.value.contains("x") {
            let long_constant_str: String;
            if long_constant.is_neg {
                long_constant_str = format!("-{}", &long_constant.value[2..]);
            } else {
                long_constant_str = long_constant.value[2..].to_string();
            }
            match i64::from_str_radix(long_constant_str.as_str(), 16) {
                Ok(_) => (),
                Err(_) => {
                    self.push_error(&format!(
                        "Error: Long literal {} is out of 64 bit range.",
                        long_constant.value
                    ));
                }
            }
        } else {
            let mut long_constant_str = long_constant.value.clone();
            if long_constant.is_neg {
                long_constant_str = format!("-{}", long_constant_str);
            }
            match long_constant_str.as_str().parse::<i64>() {
                Ok(_) => (),
                Err(_) => {
                    self.push_error(&format!(
                        "Error: Integer literal {} is out of 64 bit range.",
                        long_constant.value
                    ));
                }
            }
        }
        if self.checking_type {
            if self.init_type != Type::Long {
                self.push_error(&format!(
                    "Error: expected {:?} as type for initializer variable not long",
                    self.init_type
                ));
                self.result_expr_type = self.init_type.clone();
                return;
            }
        }
        self.result_expr_type = Type::Long;
    }

    fn visit_bool_constant(&mut self, _bool_constant: &AST::BoolConstant) {
        if self.checking_type {
            if self.init_type != Type::Bool {
                self.push_error(&format!(
                    "Error: expected {:?} as type for initializer variable not bool",
                    self.init_type
                ));
                self.result_expr_type = self.init_type.clone();
                return;
            }
        }
        self.result_expr_type = Type::Bool;
    }

    fn visit_char_constant(&mut self, _char_constant: &AST::CharConstant) {
        if self.checking_type {
            if self.init_type != Type::Int {
                self.push_error(&format!(
                    "Error: expected {:?} as type for initializer variable not int",
                    self.init_type
                ));
                self.result_expr_type = self.init_type.clone();
                return;
            }
        }
        self.result_expr_type = Type::Int;
    }
}

pub fn interpret_file(input: &std::path::PathBuf, debug: bool) -> Result<SymbolTable, Vec<String>> {
    let _input = std::fs::read_to_string(input).expect("Filename is incorrect.");
    match parse_file(input) {
        Ok(ast) => {
            let global_scope = Table {
                method_return_type: Type::None,
                entries: HashMap::new(),
                scope_ind: 0,
                parent_ind: None,
                children_inds: vec![],
            };
            let scopes = vec![Box::new(global_scope)];

            let mut interpreter = Interpreter {
                scopes: scopes,
                vars: vec![],
                errors: vec![],
                correct: true,
                checking_type: false,
                init_method: false,
                init_type: Type::None,
                in_loop: 0,
                in_expr: 0,
                in_location: false,
                var_count: 0,
                cur_scope_ind: 0,
                result_expr_type: Type::None,
                debug: debug,
            };

            ast.accept(&mut interpreter);

            if interpreter.correct {
                return Ok(SymbolTable {
                    vars: interpreter.vars,
                    scopes: interpreter.scopes,
                });
            } else {
                return Err(interpreter.errors);
            }
        }

        Err(errors) => {
            return Err(errors);
        }
    }
}

pub fn interpret(input: &std::path::PathBuf, mut writer: Box<dyn std::io::Write>, debug: bool) {
    match interpret_file(input, debug) {
        Ok(_) => {
            writeln!(writer, "Interpreted successfully.").unwrap();
            std::process::exit(0);
        }
        Err(errors) => {
            for error in errors {
                writeln!(writer, "{}", error).unwrap();
            }
            std::process::exit(1);
        }
    }
}
