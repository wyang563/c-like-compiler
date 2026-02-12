use super::super::parser::visitor::Visitor;
use super::super::parser::AST;
use super::super::semantics::symbol_table::{Entry as SymEntry, SymbolTable, Type as SymType};
use super::three_address_code::{
    BasicBlock, BinOp, BlockId, ConstValue, FunctionIR, GlobalDecl, GlobalKind, ICmpPred, Instr,
    InstrKind, Phi, ProgramIR, Symbol, Terminator, Type, UnOp, ValueId, ValueInfo,
};
use std::collections::{HashMap, HashSet};

/// Context information for a loop (while/for)
/// Used by break/continue to determine jump targets
#[derive(Clone, Debug)]
pub struct LoopContext {
    pub header_block: BlockId,
    pub exit_block: BlockId,
    pub continue_target: BlockId,
}

/// Context for flattening chains of the same logical operator (&&/||).
/// When a nested && (or ||) sees an existing context with the same op,
/// it short-circuits directly to the outermost merge block instead of
/// creating its own intermediate merge.
#[derive(Clone, Debug)]
struct ShortCircuitCtx {
    merge_bb: BlockId,
    short_circuit_val: ValueId,             // false for &&, true for ||
    op: String,                             // "&&" or "||"
    phi_incomings: Vec<(BlockId, ValueId)>, // accumulated short-circuit edges (bool)
    mem_phi_incomings: Vec<(BlockId, ValueId)>, // accumulated short-circuit edges (mem)
}

#[allow(non_camel_case_types)]
pub struct SSA_CFG_Compiler {
    // ==================== Final Output ====================
    program_ir: ProgramIR,

    // ==================== Symbol Table & Scope ====================
    symbol_table: SymbolTable,
    cur_scope_ind: usize,
    cur_child_scope_map: HashMap<usize, usize>, // parent scope idx -> which child scope we're on

    // ==================== Global Tracking ====================
    imported_funcs: HashSet<String>,

    // ==================== ID Generators ====================
    next_value_id: u32,
    next_block_id: u32,

    // ==================== Current Function State ====================
    cur_func: Option<FunctionIR>, // None when in global scope

    // ==================== Current Block State ====================
    cur_block_ind: usize, // Index into cur_func.blocks
    cur_mem: ValueId,     // Current memory token for threading

    // Stack of loop contexts for handling break/continue
    loop_stack: Vec<LoopContext>,

    // Track predecessor blocks for each block (needed for phi insertion in Pass 2)
    // Maps: BlockId -> Vec<BlockId> of predecessors
    block_predecessors: HashMap<BlockId, Vec<BlockId>>,

    // Maps scope index -> variable name -> current ValueId
    // Used to track which ValueId a variable currently maps to in each scope
    var_to_value_id: HashMap<usize, HashMap<String, ValueId>>,

    // ==================== Result/Temporary Storage ====================
    // These store intermediate results from visitor methods
    result_value_id: Option<ValueId>, // For expression results
    result_var_type: Type,
    result_is_global: Option<bool>, // tracks whether an identifier processed is a global
    result_literal_value: Option<ConstValue>,
    result_array_literal_values: Option<Vec<ConstValue>>,

    // ==================== Flags ====================
    init_method: bool, // True when initializing a method (for parameter handling)

    // ==================== Short-Circuit Context ====================
    short_circuit_ctx: Option<ShortCircuitCtx>,
}

impl SSA_CFG_Compiler {
    // ==================== ID Generators ====================

    fn get_next_value_id(&mut self) -> u32 {
        self.next_value_id += 1;
        return self.next_value_id - 1;
    }

    fn get_next_block_id(&mut self) -> u32 {
        self.next_block_id += 1;
        return self.next_block_id - 1;
    }

    // ==================== Result Getters/Setters ====================
    /// Get and consume the result value ID from an expression
    fn get_result_value_id(&mut self) -> ValueId {
        let value_id = self.result_value_id.expect("No result value ID available");
        self.result_value_id = None; // Reset for safety
        value_id
    }

    /// Set the result value ID for an expression
    fn set_result_value_id(&mut self, value_id: ValueId) {
        self.result_value_id = Some(value_id);
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

    // ==================== Loop Context Methods ====================

    /// Get the current loop context (panics if not in a loop)
    fn current_loop_context(&self) -> &LoopContext {
        self.loop_stack.last().expect("Not inside a loop")
    }

    /// Check if we're currently inside a loop
    fn is_in_loop(&self) -> bool {
        !self.loop_stack.is_empty()
    }

    // ==================== Block/CFG Helper Methods ====================

    /// Add a predecessor edge for phi construction later
    fn add_predecessor(&mut self, block_id: BlockId, pred_id: BlockId) {
        self.block_predecessors
            .entry(block_id)
            .or_insert_with(Vec::new)
            .push(pred_id);
    }

    /// Get the current block's ID
    fn current_block_id(&self) -> BlockId {
        self.cur_func.as_ref().expect("No current function").blocks[self.cur_block_ind].id
    }

    // ==================== Scope Management ====================
    // incrs cur_scope_ind and cur_child_scope_map to reflect
    fn next_child_scope(&mut self) {
        let cur_scope = self.symbol_table.scopes[self.cur_scope_ind].as_ref();
        let child_scope_ind_in_list = *self
            .cur_child_scope_map
            .entry(self.cur_scope_ind)
            .or_insert(0); // index of children_inds element we are on
        *self
            .cur_child_scope_map
            .get_mut(&self.cur_scope_ind)
            .expect("missing child-scope counter for parent scope") += 1;

        self.cur_scope_ind = cur_scope.children_inds[child_scope_ind_in_list];
    }

    fn decrement_to_parent_scope(&mut self) {
        let cur_scope = self.symbol_table.scopes[self.cur_scope_ind].as_ref();
        self.cur_scope_ind = cur_scope.parent_ind.unwrap();
    }

    // get entry from a given scope index
    fn get_scope_entry(&self, scope_ind: usize, var_name: &str) -> &SymEntry {
        let scope = self.symbol_table.scopes[scope_ind].as_ref();
        match scope.entries.get(var_name) {
            Some(entry) => entry,
            None => {
                eprintln!(
                    "Error: variable {} not found in scope {}",
                    var_name, scope_ind
                );
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
                    eprintln!(
                        "Error: variable {} not found in any scope starting at {}",
                        var_name, self.cur_scope_ind
                    );
                    panic!();
                }
            }
        }
    }

    // ==================== CFG Construction Helpers ====================

    /// Create a new basic block with a specific pre-allocated block ID
    /// and set it as the current block
    fn start_block_with_id(&mut self, block_id: BlockId) -> usize {
        let new_bb = BasicBlock {
            id: block_id,
            mem_in: None,
            phis: vec![],
            instrs: vec![],
            term: Terminator::Unreachable,
        };

        self.cur_func.as_mut().unwrap().blocks.push(new_bb);
        self.cur_block_ind = self.cur_func.as_ref().unwrap().blocks.len() - 1;
        self.cur_func
            .as_mut()
            .unwrap()
            .block_id_to_ind
            .insert(block_id, self.cur_block_ind);

        return self.cur_block_ind;
    }

    // ==================== Instruction Emission Helpers ====================

    /// Create a new SSA value, register it in the current function's values map
    fn new_value(&mut self, ty: Type, name: &str) -> ValueId {
        let id = ValueId(self.get_next_value_id());
        let info = ValueInfo {
            ty,
            declared_location: None,
            use_chain: vec![],
            org_name: name.to_string(),
            debug_name: name.to_string(),
        };
        self.cur_func.as_mut().unwrap().values.insert(id, info);
        id
    }

    /// Emit an instruction into the current basic block
    fn emit_instr(&mut self, results: Vec<ValueId>, kind: InstrKind) {
        let instr = Instr { results, kind };
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
            .instrs
            .push(instr);
    }

    /// Read a scalar variable's current value (local: lookup, global: GlobalAddr + Load)
    fn read_scalar_var(
        &mut self,
        var_name: &str,
        var_scope_ind: usize,
        is_global: bool,
        var_type: &Type,
    ) -> ValueId {
        if is_global {
            let addr = self.new_value(Type::Ptr(Box::new(var_type.clone())), var_name);
            self.emit_instr(
                vec![addr],
                InstrKind::GlobalAddr {
                    sym: Symbol(var_name.to_string()),
                    ty: var_type.clone(),
                },
            );
            let mem_in = self.cur_mem;
            let mem_out = self.new_value(Type::Mem, "");
            let load_result = self.new_value(var_type.clone(), var_name);
            self.emit_instr(
                vec![mem_out, load_result],
                InstrKind::Load {
                    ty: var_type.clone(),
                    mem: mem_in,
                    addr,
                },
            );
            self.cur_mem = mem_out;
            load_result
        } else {
            *self
                .var_to_value_id
                .get(&var_scope_ind)
                .and_then(|scope_map| scope_map.get(var_name))
                .unwrap_or_else(|| {
                    panic!("Variable {} not found in scope {}", var_name, var_scope_ind)
                })
        }
    }

    /// Write a value to a global scalar variable (GlobalAddr + Store)
    fn write_global_scalar(&mut self, var_name: &str, var_type: &Type, value: ValueId) {
        let addr = self.new_value(Type::Ptr(Box::new(var_type.clone())), var_name);
        self.emit_instr(
            vec![addr],
            InstrKind::GlobalAddr {
                sym: Symbol(var_name.to_string()),
                ty: var_type.clone(),
            },
        );
        let mem_in = self.cur_mem;
        let mem_out = self.new_value(Type::Mem, "");
        self.emit_instr(
            vec![mem_out],
            InstrKind::Store {
                ty: var_type.clone(),
                mem: mem_in,
                addr,
                value,
            },
        );
        self.cur_mem = mem_out;
    }

    /// After visiting a literal (which sets result_literal_value),
    /// emit a Const instruction and set the result value ID.
    fn emit_const_from_literal(&mut self, ty: Type) {
        let const_val = self.get_literal_value();
        let result = self.new_value(ty, "");
        self.emit_instr(vec![result], InstrKind::Const(const_val));
        self.set_result_value_id(result);
    }

    fn is_terminator_unreachable(&self) -> bool {
        let cur_terminator = self.cur_func.as_ref().unwrap().blocks[self.cur_block_ind]
            .term
            .clone();
        return cur_terminator == Terminator::Unreachable;
    }

    /// Map a compound assignment operator string to the corresponding BinOp
    fn compound_assign_to_binop(op: &str) -> BinOp {
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
            kind: GlobalKind::GlobalStr { bytes },
        });
    }

    fn visit_field_decl(&mut self, field_decl: &AST::FieldDecl) {
        for var_decl in &field_decl.vars {
            self.visit_var_decl(var_decl);
        }
    }

    fn visit_method_decl(&mut self, method_decl: &AST::MethodDecl) {
        self.init_method = true;
        self.visit_identifier(&method_decl.name); // bookeeping for method name (idt we actually need to call this)
        let method_name = method_decl.name.name.clone();
        let method_type = self.get_result_var_type();

        // create new CFG in FunctionIR
        let function_ir = FunctionIR {
            name: Symbol(method_name.clone()),
            params: vec![],
            ret_ty: method_type.clone(),
            values: HashMap::new(),
            blocks: vec![],
            block_id_to_ind: HashMap::new(),
            blocks_map: HashMap::new(),
        };

        self.cur_func = Some(function_ir);

        // increment scope and add method args to new scope
        self.next_child_scope();
        for method_arg in &method_decl.args {
            self.visit_method_arg_decl(method_arg);
        }

        self.cur_mem = self.new_value(Type::Mem, ""); // initialize memory token for function

        // Create entry block for function
        let entry_block_id = BlockId(self.get_next_block_id());
        self.start_block_with_id(entry_block_id);

        // visit function block
        self.visit_block(method_decl.body.as_ref());

        // insert terminal return node if not already
        if self.is_terminator_unreachable() {
            let mem = self.new_value(Type::Mem, "");
            let cur_node = &mut self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind];
            cur_node.term = Terminator::RetVoid { mem };
        }

        // insert into functions in program IR
        let func_ir = self.cur_func.take().unwrap();
        self.program_ir
            .functions
            .insert(method_name.clone(), func_ir);
    }

    fn visit_block(&mut self, block: &AST::Block) {
        // if not init method increment scope
        if !self.init_method {
            self.next_child_scope();
        }
        self.init_method = false;

        // visit all field declarations
        for field_decl in &block.fields {
            self.visit_field_decl(field_decl);
        }

        // visit all statements
        for statement in &block.statements {
            if !self.is_terminator_unreachable() {
                break;
            }
            statement.accept(self);
        }

        // decrement back to parent scope
        self.decrement_to_parent_scope();
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
                let init_array_len_str =
                    var_decl.array_len.as_ref().as_ref().unwrap().value.clone();
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
                    }
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
                }
                Type::Ptr(elem_ty) => {
                    let global_decl = GlobalDecl {
                        sym: Symbol(var_name),
                        kind: GlobalKind::GlobalArray {
                            elem_ty: *elem_ty,
                            len: init_array_len.unwrap() as u32,
                            init: init_array_values.clone(),
                        },
                    };
                    self.program_ir.globals.push(global_decl);
                }
                _ => {
                    eprintln!("Error: invalid global variable type");
                    panic!();
                }
            }
        }
        // NOTE - since I was dumb and didn't realize we can't initialize variables with values we don't need to do
        // anything more here for the case of local variable declarations.
    }

    fn visit_method_arg_decl(&mut self, method_arg_decl: &AST::MethodArgDecl) {
        self.visit_identifier(method_arg_decl.name.as_ref());
    }

    fn visit_if_statement(&mut self, if_statement: &AST::IfStatement) {
        let entry_block_id = self.current_block_id();

        // Evaluate the condition expression in the current block
        self.visit_expression(&if_statement.condition);
        let cond_value = self.get_result_value_id();

        // Pre-allocate block IDs for then, else (if needed), and merge blocks
        let then_bb_id = BlockId(self.get_next_block_id());
        let merge_bb_id = BlockId(self.get_next_block_id());
        let else_bb_id = if if_statement.else_block.as_ref().is_some() {
            BlockId(self.get_next_block_id())
        } else {
            merge_bb_id // If no else clause, false branch goes directly to merge
        };

        // Set the conditional branch terminator on the current (entry) block
        let mem = self.new_value(Type::Mem, "");
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::CBr {
            mem,
            cond: cond_value,
            then_bb: then_bb_id,
            else_bb: else_bb_id,
        };

        // Record predecessor edges for phi insertion later
        self.add_predecessor(then_bb_id, entry_block_id);
        if if_statement.else_block.as_ref().is_some() {
            self.add_predecessor(else_bb_id, entry_block_id);
        } else {
            // If no else, entry goes directly to merge on false branch
            self.add_predecessor(merge_bb_id, entry_block_id);
        }

        // Create and visit the 'then' block
        self.start_block_with_id(then_bb_id);
        self.visit_block(if_statement.then_block.as_ref());

        // Terminate then block with jump to merge (if not already terminated by return/break)
        if self.is_terminator_unreachable() {
            let mem = self.new_value(Type::Mem, "");
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
                mem,
                target: merge_bb_id,
            };
            self.add_predecessor(merge_bb_id, then_bb_id);
        }

        // Create and visit the 'else' block if it exists
        if let Some(else_block) = if_statement.else_block.as_ref().as_ref() {
            self.start_block_with_id(else_bb_id);
            self.visit_block(else_block);

            // Terminate else block with jump to merge (if not already terminated)
            if self.is_terminator_unreachable() {
                let mem = self.new_value(Type::Mem, "");
                self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
                    mem,
                    target: merge_bb_id,
                };
                self.add_predecessor(merge_bb_id, else_bb_id);
            }
        }

        // Create the merge block and continue execution there
        self.start_block_with_id(merge_bb_id);
    }

    fn visit_for_statement(&mut self, _for_statement: &AST::ForStatement) {}

    fn visit_while_statement(&mut self, _while_statement: &AST::WhileStatement) {}

    fn visit_return_statement(&mut self, _return_statement: &AST::ReturnStatement) {}

    fn visit_statement_control(&mut self, _statement_control: &AST::StatementControl) {}

    fn visit_assignment(&mut self, assignment: &AST::Assignment) {
        let assign_op = assignment.assign_op.as_str();

        // Resolve the assignment target via visit_location
        // - Identifier (status 2): sets result_var_type, result_is_global
        // - IndexExpression (status 2): computes elem addr into result_value_id,
        //   sets result_var_type to elem type, result_is_global
        self.visit_location(assignment.assign_var.as_ref());
        let var_type = self.get_result_var_type();
        let is_global = self.get_is_global();

        // For ++/--, the RHS is implicit (constant 1). Otherwise, evaluate the RHS expression.
        let is_inc_dec = assign_op == "++" || assign_op == "--";
        let mut rhs_value = if is_inc_dec {
            // Emit constant 1 matching the variable's type
            let one_const = match &var_type {
                Type::I32 => ConstValue::I32(1),
                Type::I64 => ConstValue::I64(1),
                _ => {
                    eprintln!("Error: ++/-- on non-integer type");
                    panic!();
                }
            };
            let one = self.new_value(var_type.clone(), "");
            self.emit_instr(vec![one], InstrKind::Const(one_const));
            one
        } else {
            let expr = assignment
                .expr
                .as_ref()
                .as_ref()
                .expect("assignment missing RHS expression");
            self.visit_expression(expr);
            self.get_result_value_id()
        };

        match assignment.assign_var.as_ref() {
            // Scalar variable assignment
            AST::ASTNode::Identifier(identifier) => {
                let var_name = &identifier.name;
                let var_scope_ind = self.get_var_scope_ind(var_name);

                // Handle compound assignments (+=, -=, *=, /=, %=, ++, --)
                if assign_op != "=" {
                    let current_value =
                        self.read_scalar_var(var_name, var_scope_ind, is_global, &var_type);
                    let bin_op = Self::compound_assign_to_binop(assign_op);
                    let result = self.new_value(var_type.clone(), var_name);
                    self.emit_instr(
                        vec![result],
                        InstrKind::BinOp {
                            op: bin_op,
                            ty: var_type.clone(),
                            lhs: current_value,
                            rhs: rhs_value,
                        },
                    );
                    rhs_value = result;
                }

                // Write the result back
                if is_global {
                    self.write_global_scalar(var_name, &var_type, rhs_value);
                } else {
                    self.var_to_value_id
                        .entry(var_scope_ind)
                        .or_insert_with(HashMap::new)
                        .insert(var_name.to_string(), rhs_value);
                }
            }

            // Array element assignment
            AST::ASTNode::IndexExpression(_) => {
                // visit_index_expression (status 2) put the elem addr in result_value_id
                let elem_addr = self.get_result_value_id();

                // Handle compound assignments
                if assign_op != "=" {
                    // Load current value from element address
                    let mem_in = self.cur_mem;
                    let mem_out = self.new_value(Type::Mem, "");
                    let current_value = self.new_value(var_type.clone(), "");
                    self.emit_instr(
                        vec![mem_out, current_value],
                        InstrKind::Load {
                            ty: var_type.clone(),
                            mem: mem_in,
                            addr: elem_addr,
                        },
                    );
                    self.cur_mem = mem_out;

                    let bin_op = Self::compound_assign_to_binop(assign_op);
                    let result = self.new_value(var_type.clone(), "");
                    self.emit_instr(
                        vec![result],
                        InstrKind::BinOp {
                            op: bin_op,
                            ty: var_type.clone(),
                            lhs: current_value,
                            rhs: rhs_value,
                        },
                    );
                    rhs_value = result;
                }

                // Store the result to element address
                let mem_in = self.cur_mem;
                let mem_out = self.new_value(Type::Mem, "");
                self.emit_instr(
                    vec![mem_out],
                    InstrKind::Store {
                        ty: var_type,
                        mem: mem_in,
                        addr: elem_addr,
                        value: rhs_value,
                    },
                );
                self.cur_mem = mem_out;
            }

            _ => {
                eprintln!("Error: invalid assignment target");
                panic!();
            }
        }
    }

    fn visit_expression(&mut self, expr: &AST::ASTNode) {
        match expr {
            AST::ASTNode::BinaryExpression(binary_expr) => {
                self.visit_binary_expression(binary_expr);
            }
            AST::ASTNode::UnaryExpression(unary_expr) => {
                self.visit_unary_expression(unary_expr);
            }
            AST::ASTNode::MethodCall(method_call) => {
                self.visit_method_call(method_call);
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
            AST::ASTNode::IndexExpression(index_expr) => {
                self.visit_index_expression(index_expr);
            }

            // Literals - parse value, emit Const instruction, set result_value_id
            AST::ASTNode::IntConstant(int_constant) => {
                self.visit_int_constant(int_constant);
                self.emit_const_from_literal(Type::I32);
            }
            AST::ASTNode::LongConstant(long_constant) => {
                self.visit_long_constant(long_constant);
                self.emit_const_from_literal(Type::I64);
            }
            AST::ASTNode::BoolConstant(bool_constant) => {
                self.visit_bool_constant(bool_constant);
                self.emit_const_from_literal(Type::I1);
            }
            AST::ASTNode::CharConstant(char_constant) => {
                self.visit_char_constant(char_constant);
                self.emit_const_from_literal(Type::I32);
            }

            // Identifier in expression context (read) - handled by visit_identifier status=1
            AST::ASTNode::Identifier(identifier) => {
                self.visit_identifier(identifier);
            }

            _ => {
                eprintln!("Error: unexpected expression node: {:?}", expr);
                panic!();
            }
        }
    }

    fn visit_method_call(&mut self, method_call: &AST::MethodCall) {
        let method_name = method_call.name.name.clone();
        let is_imported = self.imported_funcs.contains(&method_name);

        // Look up return type from symbol table (methods are in global scope 0)
        let entry = self.get_scope_entry(0, &method_name);
        let ret_ty = match &entry.get_type() {
            SymType::Int => Type::I32,
            SymType::Long => Type::I64,
            SymType::Bool => Type::I1,
            SymType::Void => Type::Void,
            _ => {
                eprintln!("Error: invalid method return type for {}", method_name);
                panic!();
            }
        };

        // Evaluate arguments
        let mut arg_values: Vec<ValueId> = vec![];
        for arg in &method_call.args {
            match arg.as_ref() {
                // String literal arguments (only valid for imported calls)
                AST::ASTNode::StringConstant(string_constant) => {
                    // Create a global string constant and pass its address
                    let str_name = format!(".str_{}", self.program_ir.globals.len());
                    let mut bytes: Vec<i8> = string_constant
                        .value
                        .as_bytes()
                        .iter()
                        .map(|b| *b as i8)
                        .collect();
                    bytes.push(0);
                    self.program_ir.globals.push(GlobalDecl {
                        sym: Symbol(str_name.clone()),
                        kind: GlobalKind::GlobalStr { bytes },
                    });
                    let str_addr = self.new_value(Type::Ptr(Box::new(Type::I8)), &str_name);
                    self.emit_instr(
                        vec![str_addr],
                        InstrKind::GlobalStrAddr {
                            sym: Symbol(str_name),
                        },
                    );
                    arg_values.push(str_addr);
                }
                // Regular expression arguments
                _ => {
                    self.visit_expression(arg);
                    arg_values.push(self.get_result_value_id());
                }
            }
        }

        // Emit the call instruction
        let mem_in = self.cur_mem;
        let mem_out = self.new_value(Type::Mem, "");

        let is_void = ret_ty == Type::Void;
        let instr_kind = if is_imported {
            InstrKind::CallImport {
                mem: mem_in,
                callee: Symbol(method_name),
                args: arg_values,
                ret_ty: ret_ty.clone(),
            }
        } else {
            InstrKind::Call {
                mem: mem_in,
                callee: Symbol(method_name),
                args: arg_values,
                ret_ty: ret_ty.clone(),
            }
        };

        if is_void {
            self.emit_instr(vec![mem_out], instr_kind);
        } else {
            let ret_val = self.new_value(ret_ty, "call");
            self.emit_instr(vec![mem_out, ret_val], instr_kind);
            self.set_result_value_id(ret_val);
        }
        self.cur_mem = mem_out;
    }

    fn visit_len_call(&mut self, len_call: &AST::LenCall) {
        let array_name = len_call.id.name.as_str();
        let result = self.new_value(Type::I32, "len");
        self.emit_instr(
            vec![result],
            InstrKind::Len {
                sym: Symbol(array_name.to_string()),
            },
        );
        self.set_result_value_id(result);
    }

    fn visit_int_cast(&mut self, _int_cast: &AST::IntCast) {}

    fn visit_long_cast(&mut self, _long_cast: &AST::LongCast) {}

    fn visit_unary_expression(&mut self, unary_expression: &AST::UnaryExpression) {
        let op = unary_expression.op.as_str();

        self.visit_expression(&unary_expression.expr);
        let arg_val = self.get_result_value_id();

        let operand_ty = self.cur_func.as_ref().unwrap().values[&arg_val].ty.clone();

        match op {
            // Negation operator (works on int and long)
            "-" => {
                let unary_op = UnOp::Neg;
                let result = self.new_value(operand_ty.clone(), "neg");
                self.emit_instr(
                    vec![result],
                    InstrKind::UnOp {
                        op: unary_op,
                        ty: operand_ty,
                        arg: arg_val,
                    },
                );
                self.set_result_value_id(result);
            }

            // Logical NOT operator (works on bool)
            "!" => {
                let unary_op = UnOp::Not;
                let result = self.new_value(Type::I1, "not");
                self.emit_instr(
                    vec![result],
                    InstrKind::UnOp {
                        op: unary_op,
                        ty: Type::I1,
                        arg: arg_val,
                    },
                );
                self.set_result_value_id(result);
            }

            _ => {
                eprintln!("Error: unknown unary operator '{}'", op);
                panic!();
            }
        }
    }

    fn visit_binary_expression(&mut self, binary_expression: &AST::BinaryExpression) {
        let op = binary_expression.op.as_str();

        match op {
            // Arithmetic operators
            "+" | "-" | "*" | "/" | "%" => {
                self.visit_expression(&binary_expression.left_expr);
                let lhs_val = self.get_result_value_id();

                self.visit_expression(&binary_expression.right_expr);
                let rhs_val = self.get_result_value_id();

                let operand_ty = self.cur_func.as_ref().unwrap().values[&lhs_val].ty.clone();

                let bin_op = match op {
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "*" => BinOp::Mul,
                    "/" => BinOp::SDiv,
                    "%" => BinOp::SRem,
                    _ => unreachable!(),
                };

                let result = self.new_value(operand_ty.clone(), "binop");
                self.emit_instr(
                    vec![result],
                    InstrKind::BinOp {
                        op: bin_op,
                        ty: operand_ty,
                        lhs: lhs_val,
                        rhs: rhs_val,
                    },
                );
                self.set_result_value_id(result);
            }

            // Comparison operators
            "<" | "<=" | ">" | ">=" | "==" | "!=" => {
                self.visit_expression(&binary_expression.left_expr);
                let lhs_val = self.get_result_value_id();

                self.visit_expression(&binary_expression.right_expr);
                let rhs_val = self.get_result_value_id();

                let operand_ty = self.cur_func.as_ref().unwrap().values[&lhs_val].ty.clone();

                let pred = match op {
                    "<" => ICmpPred::Lt,
                    "<=" => ICmpPred::Le,
                    ">" => ICmpPred::Gt,
                    ">=" => ICmpPred::Ge,
                    "==" => ICmpPred::Eq,
                    "!=" => ICmpPred::Ne,
                    _ => unreachable!(),
                };

                let result = self.new_value(Type::I1, "cmp");
                self.emit_instr(
                    vec![result],
                    InstrKind::ICmp {
                        pred,
                        ty: operand_ty,
                        lhs: lhs_val,
                        rhs: rhs_val,
                    },
                );
                self.set_result_value_id(result);
            }

            // Logical operators with short-circuit evaluation.
            // Chains of the same operator (e.g. a && b && c) are flattened:
            // all short-circuit exits jump directly to a single merge block.
            "&&" | "||" => {
                let is_and = op == "&&";
                let is_nested = matches!(&self.short_circuit_ctx, Some(ctx) if ctx.op == op);

                // Setup: determine merge block, short-circuit value, and save prev context
                let (merge_bb, sc_val, prev_ctx) = if is_nested {
                    // Nested: reuse outer context
                    let ctx = self.short_circuit_ctx.as_ref().unwrap();
                    (ctx.merge_bb, ctx.short_circuit_val, None)
                } else {
                    // Outermost: create new context
                    let merge_bb_id = BlockId(self.get_next_block_id());
                    let sc_const = ConstValue::I1(!is_and); // false for &&, true for ||
                    let sc_val = self.new_value(Type::I1, "short_circuit");
                    self.emit_instr(vec![sc_val], InstrKind::Const(sc_const));

                    let prev_ctx = self.short_circuit_ctx.take();
                    self.short_circuit_ctx = Some(ShortCircuitCtx {
                        merge_bb: merge_bb_id,
                        short_circuit_val: sc_val,
                        op: op.to_string(),
                        phi_incomings: vec![],
                        mem_phi_incomings: vec![],
                    });
                    (merge_bb_id, sc_val, Some(prev_ctx))
                };

                // Evaluate LHS and emit conditional branch
                self.visit_expression(&binary_expression.left_expr);
                let lhs_val = self.get_result_value_id();
                let lhs_block_id = self.current_block_id();

                let rhs_bb_id = BlockId(self.get_next_block_id());
                let (then_bb, else_bb) = if is_and {
                    (rhs_bb_id, merge_bb) // &&: true→RHS, false→merge
                } else {
                    (merge_bb, rhs_bb_id) // ||: true→merge, false→RHS
                };

                let mem = self.new_value(Type::Mem, "");
                self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::CBr {
                    mem,
                    cond: lhs_val,
                    then_bb,
                    else_bb,
                };
                self.add_predecessor(rhs_bb_id, lhs_block_id);
                self.add_predecessor(merge_bb, lhs_block_id);
                let sc_mem = self.cur_mem;
                let ctx = self.short_circuit_ctx.as_mut().unwrap();
                ctx.phi_incomings.push((lhs_block_id, sc_val));
                ctx.mem_phi_incomings.push((lhs_block_id, sc_mem));

                // Evaluate RHS
                self.start_block_with_id(rhs_bb_id);
                self.visit_expression(&binary_expression.right_expr);
                let rhs_val = self.get_result_value_id();

                // Finalize: outermost creates merge block, nested just returns
                if let Some(prev_ctx) = prev_ctx {
                    // Outermost: finalize merge block and phi
                    let rhs_block_id = self.current_block_id();
                    let rhs_mem = self.cur_mem;
                    let mem = self.new_value(Type::Mem, "");
                    self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term =
                        Terminator::Br {
                            mem,
                            target: merge_bb,
                        };
                    self.add_predecessor(merge_bb, rhs_block_id);

                    let sc_ctx = self.short_circuit_ctx.take().unwrap();
                    let mut phi_incomings = sc_ctx.phi_incomings;
                    let mut mem_phi_incomings = sc_ctx.mem_phi_incomings;
                    phi_incomings.push((rhs_block_id, rhs_val));
                    mem_phi_incomings.push((rhs_block_id, rhs_mem));

                    self.short_circuit_ctx = prev_ctx; // Restore
                    self.start_block_with_id(merge_bb);

                    // Boolean result phi
                    let phi_result = self.new_value(Type::I1, "logic");
                    self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
                        .phis
                        .push(Phi {
                            result: phi_result,
                            ty: Type::I1,
                            incomings: phi_incomings,
                        });

                    // Memory phi to merge memory tokens from all paths
                    let mem_phi_result = self.new_value(Type::Mem, "");
                    self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
                        .phis
                        .push(Phi {
                            result: mem_phi_result,
                            ty: Type::Mem,
                            incomings: mem_phi_incomings,
                        });
                    self.cur_mem = mem_phi_result;

                    self.set_result_value_id(phi_result);
                } else {
                    // Nested: just return RHS value
                    self.set_result_value_id(rhs_val);
                }
            }

            _ => {
                eprintln!("Error: unknown binary operator '{}'", op);
                panic!();
            }
        }
    }

    fn visit_index_expression(&mut self, index_expression: &AST::IndexExpression) {
        let array_name = index_expression.id.name.as_str();
        let var_scope_ind = self.get_var_scope_ind(array_name);
        let entry = self.get_scope_entry(var_scope_ind, array_name);

        // Get element type from array type
        let elem_type = match &entry.get_type() {
            SymType::IntArray => Type::I32,
            SymType::LongArray => Type::I64,
            SymType::BoolArray => Type::I1,
            _ => {
                eprintln!("Error: index expression on non-array type");
                panic!();
            }
        };

        let is_global = var_scope_ind == 0;

        // Evaluate the index expression first (may clobber result fields)
        self.visit_expression(&index_expression.idx_expr);
        let index_value = self.get_result_value_id();

        // Get array base address
        let base_addr = if is_global {
            let addr = self.new_value(Type::Ptr(Box::new(elem_type.clone())), array_name);
            self.emit_instr(
                vec![addr],
                InstrKind::GlobalArrayAddr {
                    sym: Symbol(array_name.to_string()),
                    elem_ty: elem_type.clone(),
                },
            );
            addr
        } else {
            // For local arrays, read the base pointer from the variable mapping
            self.read_scalar_var(
                array_name,
                var_scope_ind,
                is_global,
                &Type::Ptr(Box::new(elem_type.clone())),
            )
        };

        // Compute element address
        let elem_addr = self.new_value(Type::Ptr(Box::new(elem_type.clone())), "");
        self.emit_instr(
            vec![elem_addr],
            InstrKind::ElemAddr {
                elem_ty: elem_type.clone(),
                base: base_addr,
                index: index_value,
            },
        );

        // Set result fields after sub-expressions are evaluated
        self.result_var_type = elem_type.clone();
        self.result_is_global = Some(is_global);

        match index_expression.id.status {
            // Read: load value from element address
            1 => {
                let mem_in = self.cur_mem;
                let mem_out = self.new_value(Type::Mem, "");
                let loaded_value = self.new_value(elem_type, "");
                self.emit_instr(
                    vec![mem_out, loaded_value],
                    InstrKind::Load {
                        ty: self.result_var_type.clone(),
                        mem: mem_in,
                        addr: elem_addr,
                    },
                );
                self.cur_mem = mem_out;
                self.set_result_value_id(loaded_value);
            }
            // Write: return element address for caller to store to
            2 => {
                self.set_result_value_id(elem_addr);
            }
            _ => {
                eprintln!("Error: invalid index expression id status");
                panic!();
            }
        }
    }

    fn visit_array_literal(&mut self, array_literal: &AST::ArrayLiteral) {
        let mut literal_values: Vec<ConstValue> = vec![];
        for literal in &array_literal.array_values {
            self.visit_literal(literal);
            literal_values.push(self.get_literal_value());
        }
        self.result_array_literal_values = Some(literal_values);
    }

    fn visit_location(&mut self, location: &AST::ASTNode) {
        match location {
            AST::ASTNode::Identifier(identifier) => {
                self.visit_identifier(identifier);
            }
            AST::ASTNode::IndexExpression(index_expr) => {
                self.visit_index_expression(index_expr);
            }
            _ => {
                eprintln!("Error: invalid location node: {:?}", location);
                panic!();
            }
        }
    }

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
        let entry = self.get_scope_entry(var_scope_ind, id_name);

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
            // declare: allocate a new SSA value for this variable
            0 => {
                if !is_global {
                    let new_value_id = self.get_next_value_id();

                    // if we are initializing a method then push the parameters as value ids
                    if self.init_method {
                        self.cur_func
                            .as_mut()
                            .unwrap()
                            .params
                            .push(ValueId(new_value_id));
                    }

                    self.var_to_value_id
                        .entry(var_scope_ind)
                        .or_insert(HashMap::new())
                        .insert(id_name.to_string(), ValueId(new_value_id));

                    // put newly declared variable in FunctionIR values map
                    let new_value_info = ValueInfo {
                        ty: self.result_var_type.clone(),
                        declared_location: None,
                        use_chain: vec![],
                        org_name: id_name.to_string(),
                        debug_name: id_name.to_string(),
                    };
                    self.cur_func
                        .as_mut()
                        .unwrap()
                        .values
                        .insert(ValueId(new_value_id), new_value_info);
                }
            }
            // read: look up or load the variable's current value
            1 => {
                let var_type = self.result_var_type.clone();
                let value = self.read_scalar_var(id_name, var_scope_ind, is_global, &var_type);
                self.set_result_value_id(value);
            }
            // write target: just resolve metadata (result_var_type, result_is_global)
            // the actual write is handled by the caller (visit_assignment)
            2 => {}
            _ => {
                eprintln!("Error: invalid identifier status must be one of (0, 1, 2)");
                panic!();
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
        // Output
        program_ir: ProgramIR {
            globals: vec![],
            functions: HashMap::new(),
        },

        // Symbol table
        symbol_table,
        cur_scope_ind: 0,
        cur_child_scope_map: HashMap::new(),

        // Global tracking
        imported_funcs: HashSet::new(),

        // ID generators
        next_value_id: 0,
        next_block_id: 0,

        // Function state
        cur_func: None,

        // Block state
        cur_block_ind: 0,
        cur_mem: ValueId(0), // Will be initialized properly per function

        // Control flow
        loop_stack: Vec::new(),
        block_predecessors: HashMap::new(),

        // Variable tracking
        var_to_value_id: HashMap::new(),

        // Result storage
        result_value_id: None,
        result_var_type: Type::None,
        result_is_global: None,
        result_literal_value: None,
        result_array_literal_values: None,

        // Flags
        init_method: false,

        // Short-circuit context
        short_circuit_ctx: None,
    };
    ssa_cfg_compiler.visit_program(&ast);

    // TODO: Pass 2 - phi node insertion and variable renaming
    // insert_phi_nodes(&mut ssa_cfg_compiler.program_ir);

    return ssa_cfg_compiler.program_ir;
}
