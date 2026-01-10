use super::AST::{self};
use super::visitor::Visitor;

pub struct ParserPrinter {
    indent: usize,
    // flags for parser printer state
    new_line: bool,
    in_for_loop_def: bool,
    in_expr: bool,
    set_colon: bool,
}

impl ParserPrinter {
    pub fn new() -> ParserPrinter {
        ParserPrinter {
            indent: 0,
            new_line: true,
            in_for_loop_def: false,
            in_expr: false,
            set_colon: false,
        }
    }

    fn tab_print(&mut self, print_str: &str) {
        if self.new_line {
            for _ in 0..self.indent {
                print!("  ");
            }
        }
        print!("{}", print_str);
        if print_str.ends_with('\n') {
            self.new_line = true;
        } else {
            self.new_line = false;
        }
    }
}

impl Visitor for ParserPrinter {
    fn visit_program(&mut self, program: &AST::Program) {
        for import_decl in &program.imports {
            import_decl.accept(self);
        }
        for field_decl in &program.fields {
            field_decl.accept(self);
        }
        for method_decl in &program.methods {
            method_decl.accept(self);
        }
    }

    fn visit_import_decl(&mut self, import_decl: &AST::ImportDecl) {
        self.tab_print("import ");
        import_decl.import_id.accept(self);
        self.tab_print(";\n");
    }

    fn visit_field_decl(&mut self, field_decl: &AST::FieldDecl) {
        if field_decl.is_const {
            self.tab_print("const ");
        }
        self.tab_print(&field_decl.type_name);
        self.tab_print(" ");
        for (i, var_decl) in field_decl.vars.iter().enumerate() {
            var_decl.accept(self);
            if i < field_decl.vars.len() - 1 {
                self.tab_print(", ");
            }
        }
        self.tab_print(";\n");
    }

    fn visit_method_decl(&mut self, method_decl: &AST::MethodDecl) {
        self.tab_print("\n");
        self.tab_print(&method_decl.type_name);
        self.tab_print(" ");
        method_decl.name.accept(self);
        self.tab_print("(");
        for (i, arg) in method_decl.args.iter().enumerate() {
            arg.accept(self);
            if i < method_decl.args.len() - 1 {
                self.tab_print(", ");
            }
        }
        self.tab_print(") ");
        method_decl.body.accept(self);
        self.tab_print("\n");
    }

    fn visit_block(&mut self, block: &AST::Block) {
        self.tab_print("{\n");
        self.indent += 1;
        for field_decl in &block.fields {
            field_decl.accept(self);
        }
        for statement in &block.statements {
            statement.accept(self);
        }
        self.indent -= 1;
        self.tab_print("}\n");
    }

    fn visit_var_decl(&mut self, var_decl: &AST::VarDecl) {
        var_decl.name.accept(self);
        if var_decl.is_array {
            self.tab_print("[");
            if let Some(array_len_val) = var_decl.array_len.as_ref() {
                array_len_val.accept(self);
            }
            self.tab_print("]");
        }
        if let Some(init_node) = var_decl.initializer.as_ref() {
            self.tab_print(" = ");
            init_node.accept(self);
        }
    }

    fn visit_method_arg_decl(&mut self, method_arg_decl: &AST::MethodArgDecl) {
        self.tab_print(&method_arg_decl.type_name);
        self.tab_print(" ");
        method_arg_decl.name.accept(self);
    }

    fn visit_if_statement(&mut self, if_statement: &AST::IfStatement) {
        self.tab_print("if (");
        if_statement.condition.accept(self);
        self.tab_print(") ");
        if_statement.then_block.accept(self);
        if let Some(else_block) = if_statement.else_block.as_ref() {
            self.tab_print("else ");
            else_block.accept(self);
        }
    }

    fn visit_for_statement(&mut self, for_statement: &AST::ForStatement) {
        self.in_for_loop_def = true;
        self.tab_print("for (");
        for_statement.start_assignment.accept(self);
        self.tab_print("; ");
        for_statement.end_expr.accept(self);
        self.tab_print("; ");
        for_statement.update_expr.accept(self);
        self.tab_print(") ");
        self.in_for_loop_def = false;
        for_statement.block.accept(self);
    }

    fn visit_while_statement(&mut self, while_statement: &AST::WhileStatement) {
        self.tab_print("while (");
        while_statement.condition.accept(self);
        self.tab_print(") ");
        while_statement.block.accept(self);
    }

    fn visit_return_statement(&mut self, return_statement: &AST::ReturnStatement) {
        self.tab_print("return");
        if let Some(expr) = return_statement.expr.as_ref() {
            self.tab_print(" ");
            expr.accept(self);
        }
        self.tab_print(";\n");
    }

    fn visit_statement_control(&mut self, statement_control: &AST::StatementControl) {
        self.tab_print(&statement_control.op);
        self.tab_print(";\n");
    }

    fn visit_assignment(&mut self, assignment: &AST::Assignment) {
        self.set_colon = false;
        assignment.assign_var.accept(self);
        self.tab_print(" ");
        self.tab_print(&assignment.assign_op);
        if let Some(expr) = assignment.expr.as_ref() {
            self.tab_print(" ");
            expr.accept(self);
        }
        if !self.in_for_loop_def && !self.set_colon {
            self.tab_print(";\n");
        }
    }

    fn visit_method_call(&mut self, method_call: &AST::MethodCall) {
        method_call.name.accept(self);
        self.tab_print("(");
        for (i, arg) in method_call.args.iter().enumerate() {

            arg.accept(self);
            if i < method_call.args.len() - 1 {
                self.tab_print(", ");
            }
        }
        self.tab_print(")");
        if !self.in_expr {
            self.tab_print(";\n");
            self.set_colon = true;
        }
    }

    fn visit_len_call(&mut self, len_call: &AST::LenCall) {
        self.tab_print("len(");
        len_call.id.accept(self);
        self.tab_print(")");
    }

    fn visit_unary_expression(&mut self, unary_expression: &AST::UnaryExpression) {
        self.in_expr = true;
        self.tab_print(&unary_expression.op);
        unary_expression.expr.accept(self);
        self.in_expr = false;
    }

    fn visit_binary_expression(&mut self, binary_expression: &AST::BinaryExpression) {
        self.in_expr = true;
        binary_expression.left_expr.accept(self);
        self.tab_print(" ");
        self.tab_print(&binary_expression.op);
        self.tab_print(" ");
        binary_expression.right_expr.accept(self);
        self.in_expr = false;
    }

    fn visit_index_expression(&mut self, index_expression: &AST::IndexExpression) {
        self.in_expr = true;
        index_expression.id.accept(self);
        self.tab_print("[");
        index_expression.idx_expr.accept(self);
        self.tab_print("]");
        self.in_expr = false;
    }

    fn visit_array_literal(&mut self, array_literal: &AST::ArrayLiteral) {
        self.tab_print("{");
        for (i, val) in array_literal.array_values.iter().enumerate() {
            val.accept(self);
            if i < array_literal.array_values.len() - 1 {
                self.tab_print(", ");
            }
        }
        self.tab_print("}");
    }

    fn visit_identifier(&mut self, identifier: &AST::Identifier) {
        self.tab_print(&identifier.name);
    }

    fn visit_int_constant(&mut self, int_constant: &AST::IntConstant) {
        if int_constant.is_neg {
            self.tab_print("-");
        }
        self.tab_print(&int_constant.value);
    }

    fn visit_string_constant(&mut self, string_constant: &AST::StringConstant) {
        self.tab_print(&string_constant.value);
    }

    fn visit_bool_constant(&mut self, bool_constant: &AST::BoolConstant) {
        self.tab_print(&bool_constant.value.to_string());
    }

    fn visit_char_constant(&mut self, char_constant: &AST::CharConstant) {
        self.tab_print(&char_constant.value);
    }
}



