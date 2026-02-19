use super::super::parser::visitor::Visitor;
use super::super::parser::AST;
use super::super::semantics::symbol_table::{Entry as SymEntry, SymbolTable, Type as SymType};
use super::three_address_code::{
    BasicBlock, BinOp, BlockId, CastKind, ConstValue, FunctionIR, GlobalDecl, GlobalKind, ICmpPred,
    Instr, InstrId, InstrKind, Phi, ProgramIR, Symbol, Terminator, Type, UnOp, ValueId, ValueInfo,
};
use super::utils::{
    compound_assign_to_binop, is_generic_value_name, lookup_snapshot_var, process_string_literal,
};
use std::collections::{HashMap, HashSet};

/// Context information for a loop (while/for)
/// Used by break/continue to determine jump targets
#[derive(Clone, Debug)]
pub struct LoopContext {
    #[allow(dead_code)]
    pub header_block: BlockId,
    pub exit_block: BlockId,
    pub continue_target: BlockId,
    /// (from_block, mem_at_break, var_snapshot) for each break statement
    pub break_edges: Vec<(BlockId, ValueId, Vec<(usize, String, ValueId)>)>,
    /// (from_block, mem_at_continue, var_snapshot) for each continue statement
    pub continue_edges: Vec<(BlockId, ValueId, Vec<(usize, String, ValueId)>)>,
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
    pub program_ir: ProgramIR,

    // ==================== Symbol Table & Scope ====================
    symbol_table: SymbolTable,
    cur_scope_ind: usize,
    cur_child_scope_map: HashMap<usize, usize>, // parent scope idx -> which child scope we're on

    // ==================== Global Tracking ====================
    imported_funcs: HashSet<String>,

    // ==================== ID Generators ====================
    next_value_id: u32,
    next_block_id: u32,
    next_instr_id: u32,

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

    fn get_next_instr_id(&mut self) -> u32 {
        self.next_instr_id += 1;
        return self.next_instr_id - 1;
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
    #[allow(dead_code)]
    fn current_loop_context(&self) -> &LoopContext {
        self.loop_stack.last().expect("Not inside a loop")
    }

    /// Check if we're currently inside a loop
    #[allow(dead_code)]
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
    fn start_block_with_id(&mut self, block_id: BlockId, label: &str) -> usize {
        let new_bb = BasicBlock {
            id: block_id,
            label: label.to_string(),
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
            declared_by: None, // Will be set when instruction/phi is created
            use_chain: vec![],
            org_name: name.to_string(),
            debug_name: name.to_string(),
        };
        self.cur_func.as_mut().unwrap().values.insert(id, info);
        id
    }

    /// Emit an instruction into the current basic block
    fn emit_instr(&mut self, results: Vec<ValueId>, kind: InstrKind) {
        let instr_id = InstrId(self.get_next_instr_id());
        let instr = Instr {
            id: instr_id,
            results: results.clone(),
            kind,
        };
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
            .instrs
            .push(instr);

        // Set declared_by for all result values
        for result_id in results {
            if let Some(value_info) = self.cur_func.as_mut().unwrap().values.get_mut(&result_id) {
                value_info.declared_by = Some(instr_id);
            }
        }
    }

    /// Create block map
    fn create_block_map(&mut self) {
        let block_successors: Vec<(BlockId, Vec<BlockId>)> = self
            .cur_func
            .as_ref()
            .unwrap()
            .blocks
            .iter()
            .map(|block| {
                let successors = match &block.term {
                    Terminator::Br { target, .. } => vec![*target],
                    Terminator::CBr {
                        then_bb, else_bb, ..
                    } => vec![*then_bb, *else_bb],
                    Terminator::Ret { .. }
                    | Terminator::RetVoid { .. }
                    | Terminator::Unreachable => vec![],
                };
                (block.id, successors)
            })
            .collect();

        // Now populate the map
        for (block_id, successors) in block_successors {
            self.cur_func
                .as_mut()
                .unwrap()
                .blocks_map
                .insert(block_id, successors);
        }
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

    // ==================== Break/Continue & Phi Helpers ====================

    /// Snapshot all current variable mappings into a flat vec.
    fn snapshot_vars(&self) -> Vec<(usize, String, ValueId)> {
        self.var_to_value_id
            .iter()
            .flat_map(|(&scope_ind, scope_vars)| {
                scope_vars
                    .iter()
                    .map(move |(name, &val)| (scope_ind, name.clone(), val))
            })
            .collect()
    }

    /// Patch existing phis in `target_block` with additional incomings from edges.
    /// `mem_phi_result` identifies the memory phi; `var_phis` identifies variable phis.
    fn patch_phis_from_edges(
        &mut self,
        target_block: BlockId,
        mem_phi_result: ValueId,
        var_phis: &[(usize, String, ValueId)],
        edges: &[(BlockId, ValueId, Vec<(usize, String, ValueId)>)],
    ) {
        let block_ind = *self
            .cur_func
            .as_ref()
            .unwrap()
            .block_id_to_ind
            .get(&target_block)
            .unwrap();
        for (from_block, edge_mem, var_snapshot) in edges {
            self.cur_func.as_mut().unwrap().blocks[block_ind]
                .phis
                .iter_mut()
                .find(|phi| phi.result == mem_phi_result)
                .unwrap()
                .incomings
                .push((*from_block, *edge_mem));

            for (scope_ind, var_name, phi_result) in var_phis {
                let val = lookup_snapshot_var(var_snapshot, *scope_ind, var_name);
                self.cur_func.as_mut().unwrap().blocks[block_ind]
                    .phis
                    .iter_mut()
                    .find(|phi| phi.result == *phi_result)
                    .unwrap()
                    .incomings
                    .push((*from_block, val));
            }
        }
    }

    /// Create new mem + variable phis at the current block from a list of incoming edges.
    /// Updates `cur_mem` and `var_to_value_id` to the new phi results.
    /// `var_phis` provides (scope_ind, var_name) to identify which variables need phis.
    fn emit_merge_phis(
        &mut self,
        var_phis: &[(usize, String, ValueId)],
        incomings: &[(BlockId, ValueId, Vec<(usize, String, ValueId)>)],
    ) {
        // Memory phi
        let mem_incomings: Vec<(BlockId, ValueId)> =
            incomings.iter().map(|(b, m, _)| (*b, *m)).collect();
        let mem_phi = self.new_value(Type::Mem, "");
        let mem_phi_id = InstrId(self.get_next_instr_id());
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
            .phis
            .push(Phi {
                id: mem_phi_id,
                result: mem_phi,
                ty: Type::Mem,
                incomings: mem_incomings,
            });
        // Set declared_by for memory phi
        self.cur_func
            .as_mut()
            .unwrap()
            .values
            .get_mut(&mem_phi)
            .unwrap()
            .declared_by = Some(mem_phi_id);
        self.cur_mem = mem_phi;

        // Variable phis
        for (scope_ind, var_name, _) in var_phis {
            let var_incomings: Vec<(BlockId, ValueId)> = incomings
                .iter()
                .map(|(b, _, snap)| (*b, lookup_snapshot_var(snap, *scope_ind, var_name)))
                .collect();
            let var_ty = self.cur_func.as_ref().unwrap().values[&var_incomings[0].1]
                .ty
                .clone();
            let var_phi = self.new_value(var_ty.clone(), var_name);
            let var_phi_id = InstrId(self.get_next_instr_id());
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
                .phis
                .push(Phi {
                    id: var_phi_id,
                    result: var_phi,
                    ty: var_ty,
                    incomings: var_incomings,
                });
            // Set declared_by for variable phi
            self.cur_func
                .as_mut()
                .unwrap()
                .values
                .get_mut(&var_phi)
                .unwrap()
                .declared_by = Some(var_phi_id);
            self.var_to_value_id
                .get_mut(scope_ind)
                .unwrap()
                .insert(var_name.clone(), var_phi);
        }
    }

    // ==================== Phi Elimination ====================

    /// Eliminate all phi nodes across the entire program by inserting `Assign`
    /// instructions into predecessor blocks.
    ///
    /// Must be called after `compile_to_ssa_cfg` so that `next_value_id` and
    /// `next_instr_id` are already past every allocated ID — no scanning needed.
    pub fn remove_phis(&mut self) {
        let func_names: Vec<String> = self.program_ir.functions.keys().cloned().collect();
        for func_name in func_names {
            // Temporarily move the function into cur_func so that new_value /
            // get_next_instr_id can operate on it, then put it back.
            let func = self.program_ir.functions.remove(&func_name).unwrap();
            self.cur_func = Some(func);
            self.remove_phis_in_function();
            let func = self.cur_func.take().unwrap();
            self.program_ir.functions.insert(func_name, func);
        }
    }

    /// Eliminate phi nodes in `self.cur_func`.
    ///
    /// Uses a two-phase parallel-copy approach (read-all-then-write-all) to
    /// correctly handle swap-like phis where one phi's result is an incoming
    /// value for another phi from the same predecessor.
    pub fn remove_phis_in_function(&mut self) {
        // Collect all phi copies: for each phi in every block, record one
        // (pred_id, src, dst, ty) entry per incoming edge.
        // Phi incoming values are always defined in predecessor blocks (SSA
        // invariant), so sources and destinations never alias — no temporaries
        // are needed.
        let all_copies: Vec<(BlockId, ValueId, ValueId, Type)> = {
            let func = self.cur_func.as_ref().unwrap();
            let mut result = Vec::new();
            for block in &func.blocks {
                for phi in &block.phis {
                    if matches!(phi.ty, Type::Mem | Type::Void | Type::None) {
                        continue;
                    }
                    for &(pred_id, src_val) in &phi.incomings {
                        result.push((pred_id, src_val, phi.result, phi.ty.clone()));
                    }
                }
            }
            result
        };

        // Build the Assign instructions to append to each predecessor block.
        let mut inserts: HashMap<usize, Vec<Instr>> = HashMap::new();
        for (pred_id, src, dst, ty) in all_copies {
            let pred_idx = self.cur_func.as_ref().unwrap().block_id_to_ind[&pred_id];
            let instr_id = InstrId(self.get_next_instr_id());
            inserts.entry(pred_idx).or_default().push(Instr {
                id: instr_id,
                results: vec![dst],
                kind: InstrKind::Assign { ty, src },
            });
        }

        // Append the generated Assign instructions to each predecessor block.
        let func = self.cur_func.as_mut().unwrap();
        for (pred_idx, new_instrs) in inserts {
            func.blocks[pred_idx].instrs.extend(new_instrs);
        }

        // Remove all phi nodes (both value phis and mem_in) from every block.
        for block in &mut func.blocks {
            block.phis.clear();
            block.mem_in = None;
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
        self.var_to_value_id.clear();

        // increment scope and add method args to new scope
        self.next_child_scope();
        for method_arg in &method_decl.args {
            self.visit_method_arg_decl(method_arg);
        }

        self.cur_mem = self.new_value(Type::Mem, ""); // initialize memory token for function

        // Create entry block for function
        let entry_block_id = BlockId(self.get_next_block_id());
        self.start_block_with_id(entry_block_id, "entry");

        // visit function block
        self.visit_block(method_decl.body.as_ref());

        // insert terminal return node if not already
        if self.is_terminator_unreachable() {
            let mem = self.new_value(Type::Mem, "");
            let cur_node = &mut self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind];
            cur_node.term = Terminator::RetVoid { mem };
        }

        // Populate blocks_map (successor map) before inserting into program IR
        self.create_block_map();

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

        if is_global {
            // Global variable declaration — emit into the data section
            match &var_type {
                Type::I32 | Type::I64 | Type::I1 => {
                    let global_decl = GlobalDecl {
                        sym: Symbol(var_name.clone()),
                        kind: GlobalKind::GlobalScalar {
                            ty: var_type.clone(),
                            init: init_scalar_value,
                        },
                    };
                    self.program_ir.globals.push(global_decl);
                }
                Type::Ptr(elem_ty) => {
                    let global_decl = GlobalDecl {
                        sym: Symbol(var_name.clone()),
                        kind: GlobalKind::GlobalArray {
                            elem_ty: *elem_ty.clone(),
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
        } else if var_decl.is_array {
            // Local array declaration — emit an Alloca to allocate stack space
            if let Type::Ptr(elem_ty) = &var_type {
                let array_len = init_array_len.unwrap() as u32;
                let var_scope_ind = self.get_var_scope_ind(&var_name);
                let ptr_vid = *self
                    .var_to_value_id
                    .get(&var_scope_ind)
                    .and_then(|scope_map| scope_map.get(&var_name))
                    .unwrap();
                self.emit_instr(
                    vec![ptr_vid],
                    InstrKind::Alloca {
                        elem_ty: *elem_ty.clone(),
                        count: array_len,
                    },
                );
            }
        }
    }

    fn visit_method_arg_decl(&mut self, method_arg_decl: &AST::MethodArgDecl) {
        self.visit_identifier(method_arg_decl.name.as_ref());
    }

    fn visit_if_statement(&mut self, if_statement: &AST::IfStatement) {
        let has_else = if_statement.else_block.as_ref().is_some();

        // Evaluate the condition expression in the current block
        // NOTE: if condition contains &&/||, short-circuit evaluation creates
        // new blocks, so the current block after this may differ from before.
        self.visit_expression(&if_statement.condition);
        let cond_value = self.get_result_value_id();

        // Capture the block we're in AFTER condition evaluation (may be a
        // short-circuit merge block, not the original entry block).
        let cond_block_id = self.current_block_id();

        // Snapshot entry state for phi construction at merge
        let entry_mem = self.cur_mem;
        let entry_vars = self.snapshot_vars();

        // Pre-allocate block IDs for then, else (if needed), and merge blocks
        let then_bb_id = BlockId(self.get_next_block_id());
        let merge_bb_id = BlockId(self.get_next_block_id());
        let else_bb_id = if has_else {
            BlockId(self.get_next_block_id())
        } else {
            merge_bb_id // If no else clause, false branch goes directly to merge
        };

        // Set the conditional branch terminator on the current block
        let mem = self.new_value(Type::Mem, "");
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::CBr {
            mem,
            cond: cond_value,
            then_bb: then_bb_id,
            else_bb: else_bb_id,
        };

        // Record predecessor edges (use cond_block_id, not entry_block_id)
        self.add_predecessor(then_bb_id, cond_block_id);
        if has_else {
            self.add_predecessor(else_bb_id, cond_block_id);
        } else {
            self.add_predecessor(merge_bb_id, cond_block_id);
        }

        // ── Then block ──
        self.start_block_with_id(then_bb_id, "if_then");
        self.visit_block(if_statement.then_block.as_ref());

        let then_fell_through = self.is_terminator_unreachable();
        let then_end_block_id = self.current_block_id();
        let then_end_mem = self.cur_mem;
        let then_end_vars = self.snapshot_vars();

        if then_fell_through {
            let mem = self.new_value(Type::Mem, "");
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
                mem,
                target: merge_bb_id,
            };
            self.add_predecessor(merge_bb_id, then_end_block_id);
        }

        // Restore entry state before visiting else so it sees pre-if values
        self.cur_mem = entry_mem;
        for (scope_ind, var_name, val) in &entry_vars {
            self.var_to_value_id
                .get_mut(scope_ind)
                .unwrap()
                .insert(var_name.clone(), *val);
        }

        // ── Else block (or implicit false-branch from entry) ──
        let else_fell_through: bool;
        let else_end_block_id: BlockId;
        let else_end_mem: ValueId;
        let else_end_vars: Vec<(usize, String, ValueId)>;

        if let Some(else_block) = if_statement.else_block.as_ref().as_ref() {
            self.start_block_with_id(else_bb_id, "if_else");
            self.visit_block(else_block);

            else_fell_through = self.is_terminator_unreachable();
            else_end_block_id = self.current_block_id();
            else_end_mem = self.cur_mem;
            else_end_vars = self.snapshot_vars();

            if else_fell_through {
                let mem = self.new_value(Type::Mem, "");
                self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
                    mem,
                    target: merge_bb_id,
                };
                self.add_predecessor(merge_bb_id, else_end_block_id);
            }
        } else {
            // No else: false branch flows directly from cond block to merge
            else_fell_through = true;
            else_end_block_id = cond_block_id;
            else_end_mem = entry_mem;
            else_end_vars = entry_vars.clone();
        }

        // ── Merge block with phi insertion ──
        self.start_block_with_id(merge_bb_id, "if_merge");

        let mut merge_incomings: Vec<(BlockId, ValueId, Vec<(usize, String, ValueId)>)> = vec![];
        if then_fell_through {
            merge_incomings.push((then_end_block_id, then_end_mem, then_end_vars));
        }
        if else_fell_through {
            merge_incomings.push((else_end_block_id, else_end_mem, else_end_vars));
        }

        match merge_incomings.len() {
            0 => {
                // Both branches terminated (return/break/continue) — merge is unreachable
            }
            1 => {
                // Only one branch falls through — no phi needed, just restore that branch's state
                let (_, mem, vars) = &merge_incomings[0];
                self.cur_mem = *mem;
                for (scope_ind, var_name, val) in vars {
                    self.var_to_value_id
                        .get_mut(scope_ind)
                        .unwrap()
                        .insert(var_name.clone(), *val);
                }
            }
            _ => {
                // Both branches fall through — create phis to merge variable states
                self.emit_merge_phis(&entry_vars, &merge_incomings);
            }
        }
    }

    fn visit_for_statement(&mut self, for_statement: &AST::ForStatement) {
        // Execute the init assignment in the current block
        self.visit_assignment(&for_statement.start_assignment);

        // Pre-allocate block IDs
        let header_bb_id = BlockId(self.get_next_block_id());
        let body_bb_id = BlockId(self.get_next_block_id());
        let update_bb_id = BlockId(self.get_next_block_id());
        let exit_bb_id = BlockId(self.get_next_block_id());

        // Jump from current block to header
        let entry_block_id = self.current_block_id();
        let mem = self.new_value(Type::Mem, "");
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
            mem,
            target: header_bb_id,
        };
        self.add_predecessor(header_bb_id, entry_block_id);

        // Header block: evaluate condition
        self.start_block_with_id(header_bb_id, "for_header");

        // Memory phi for the header (entry + back-edge from update)
        let mem_phi_result = self.new_value(Type::Mem, "");
        let mem_phi_id = InstrId(self.get_next_instr_id());
        let entry_mem = self.cur_mem;
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
            .phis
            .push(Phi {
                id: mem_phi_id,
                result: mem_phi_result,
                ty: Type::Mem,
                incomings: vec![(entry_block_id, entry_mem)],
            });
        self.cur_func
            .as_mut()
            .unwrap()
            .values
            .get_mut(&mem_phi_result)
            .unwrap()
            .declared_by = Some(mem_phi_id);
        self.cur_mem = mem_phi_result;

        // Variable phis for all local variables currently defined
        let var_entries = self.snapshot_vars();

        let mut var_phis: Vec<(usize, String, ValueId)> = vec![];
        for (scope_ind, var_name, entry_val) in &var_entries {
            let var_ty = self.cur_func.as_ref().unwrap().values[entry_val].ty.clone();
            let phi_result = self.new_value(var_ty.clone(), var_name);
            let phi_id = InstrId(self.get_next_instr_id());
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
                .phis
                .push(Phi {
                    id: phi_id,
                    result: phi_result,
                    ty: var_ty,
                    incomings: vec![(entry_block_id, *entry_val)],
                });
            self.cur_func
                .as_mut()
                .unwrap()
                .values
                .get_mut(&phi_result)
                .unwrap()
                .declared_by = Some(phi_id);
            var_phis.push((*scope_ind, var_name.clone(), phi_result));
        }
        for (scope_ind, var_name, phi_result) in &var_phis {
            self.var_to_value_id
                .get_mut(scope_ind)
                .unwrap()
                .insert(var_name.clone(), *phi_result);
        }

        self.visit_expression(&for_statement.end_expr);
        let cond_value = self.get_result_value_id();

        // After condition eval, current block may differ from header_bb_id
        // if the condition contained &&/|| short-circuit evaluation.
        let cond_block_id = self.current_block_id();
        let cond_mem = self.cur_mem;
        let cond_vars = self.snapshot_vars();

        // Conditional branch: true -> body, false -> exit
        let mem = self.new_value(Type::Mem, "");
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::CBr {
            mem,
            cond: cond_value,
            then_bb: body_bb_id,
            else_bb: exit_bb_id,
        };
        self.add_predecessor(body_bb_id, cond_block_id);
        self.add_predecessor(exit_bb_id, cond_block_id);

        // Body block
        self.start_block_with_id(body_bb_id, "for_body");

        // Push loop context: continue jumps to update block, not header
        self.loop_stack.push(LoopContext {
            header_block: header_bb_id,
            exit_block: exit_bb_id,
            continue_target: update_bb_id,
            break_edges: vec![],
            continue_edges: vec![],
        });

        self.visit_block(for_statement.block.as_ref());

        let loop_ctx = self.loop_stack.pop().unwrap();
        let break_edges = loop_ctx.break_edges;
        let continue_edges = loop_ctx.continue_edges;
        let has_continues = !continue_edges.is_empty();

        // Capture body end state before branching
        let body_fell_through = self.is_terminator_unreachable();
        let body_end_block_id = self.current_block_id();
        let body_end_mem = self.cur_mem;
        let body_end_vars = self.snapshot_vars();

        // Jump from body end to update block (if body fell through)
        if body_fell_through {
            let mem = self.new_value(Type::Mem, "");
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
                mem,
                target: update_bb_id,
            };
            self.add_predecessor(update_bb_id, body_end_block_id);
        }

        // Update block: merge body-end + continue edges, then execute update expr
        self.start_block_with_id(update_bb_id, "for_update");

        if has_continues {
            let mut update_incomings = vec![];
            if body_fell_through {
                update_incomings.push((body_end_block_id, body_end_mem, body_end_vars));
            }
            update_incomings.extend(continue_edges);
            self.emit_merge_phis(&var_phis, &update_incomings);
        } else if body_fell_through {
            self.cur_mem = body_end_mem;
        }

        // Execute update expression and back-edge only if update block is reachable
        if body_fell_through || has_continues {
            match for_statement.update_expr.as_ref() {
                AST::ASTNode::Assignment(assignment) => self.visit_assignment(assignment),
                AST::ASTNode::MethodCall(method_call) => self.visit_method_call(method_call),
                _ => {
                    eprintln!("Error: invalid for-update expression");
                    panic!();
                }
            }

            // Back-edge: jump from update to header
            if self.is_terminator_unreachable() {
                let update_end_block_id = self.current_block_id();
                let mem = self.new_value(Type::Mem, "");
                self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
                    mem,
                    target: header_bb_id,
                };
                self.add_predecessor(header_bb_id, update_end_block_id);

                let back_edge = vec![(update_end_block_id, self.cur_mem, self.snapshot_vars())];
                self.patch_phis_from_edges(header_bb_id, mem_phi_result, &var_phis, &back_edge);
            }
        }

        // Exit block: restore var_to_value_id to header phi results, then merge breaks
        for (scope_ind, var_name, phi_result) in &var_phis {
            self.var_to_value_id
                .get_mut(scope_ind)
                .unwrap()
                .insert(var_name.clone(), *phi_result);
        }
        self.start_block_with_id(exit_bb_id, "for_exit");

        if !break_edges.is_empty() {
            // Use cond_block_id/cond_mem/cond_vars for the normal exit path
            let mut exit_incomings = vec![(cond_block_id, cond_mem, cond_vars)];
            exit_incomings.extend(break_edges);
            self.emit_merge_phis(&var_phis, &exit_incomings);
        } else {
            self.cur_mem = cond_mem;
        }
    }

    fn visit_while_statement(&mut self, while_statement: &AST::WhileStatement) {
        // Pre-allocate block IDs
        let header_bb_id = BlockId(self.get_next_block_id());
        let body_bb_id = BlockId(self.get_next_block_id());
        let exit_bb_id = BlockId(self.get_next_block_id());

        // Jump from current block to header
        let entry_block_id = self.current_block_id();
        let mem = self.new_value(Type::Mem, "");
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
            mem,
            target: header_bb_id,
        };
        self.add_predecessor(header_bb_id, entry_block_id);

        // Header block: evaluate condition
        self.start_block_with_id(header_bb_id, "while_header");

        // Memory phi for the header (entry + back-edge from body)
        let mem_phi_result = self.new_value(Type::Mem, "");
        let mem_phi_id = InstrId(self.get_next_instr_id());
        let entry_mem = self.cur_mem;
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
            .phis
            .push(Phi {
                id: mem_phi_id,
                result: mem_phi_result,
                ty: Type::Mem,
                incomings: vec![(entry_block_id, entry_mem)],
            });
        self.cur_func
            .as_mut()
            .unwrap()
            .values
            .get_mut(&mem_phi_result)
            .unwrap()
            .declared_by = Some(mem_phi_id);
        self.cur_mem = mem_phi_result;

        // Variable phis: for each local variable currently defined, create a phi
        // so the header sees the updated value on back-edges from the body.
        // We'll patch the back-edge incoming after visiting the body.
        let var_entries = self.snapshot_vars();

        let mut var_phis: Vec<(usize, String, ValueId)> = vec![]; // (scope_ind, var_name, phi_result)
        for (scope_ind, var_name, entry_val) in &var_entries {
            let var_ty = self.cur_func.as_ref().unwrap().values[entry_val].ty.clone();
            let phi_result = self.new_value(var_ty.clone(), var_name);
            let phi_id = InstrId(self.get_next_instr_id());
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
                .phis
                .push(Phi {
                    id: phi_id,
                    result: phi_result,
                    ty: var_ty,
                    incomings: vec![(entry_block_id, *entry_val)],
                });
            self.cur_func
                .as_mut()
                .unwrap()
                .values
                .get_mut(&phi_result)
                .unwrap()
                .declared_by = Some(phi_id);
            var_phis.push((*scope_ind, var_name.clone(), phi_result));
        }
        // Update var_to_value_id to point to the phi results
        for (scope_ind, var_name, phi_result) in &var_phis {
            self.var_to_value_id
                .get_mut(scope_ind)
                .unwrap()
                .insert(var_name.clone(), *phi_result);
        }

        self.visit_expression(&while_statement.condition);
        let cond_value = self.get_result_value_id();

        // After condition eval, current block may differ from header_bb_id
        // if the condition contained &&/|| short-circuit evaluation.
        let cond_block_id = self.current_block_id();
        let cond_mem = self.cur_mem;
        let cond_vars = self.snapshot_vars();

        // Conditional branch: true -> body, false -> exit
        let mem = self.new_value(Type::Mem, "");
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::CBr {
            mem,
            cond: cond_value,
            then_bb: body_bb_id,
            else_bb: exit_bb_id,
        };
        self.add_predecessor(body_bb_id, cond_block_id);
        self.add_predecessor(exit_bb_id, cond_block_id);

        // Body block
        self.start_block_with_id(body_bb_id, "while_body");

        // Push loop context for break/continue
        self.loop_stack.push(LoopContext {
            header_block: header_bb_id,
            exit_block: exit_bb_id,
            continue_target: header_bb_id,
            break_edges: vec![],
            continue_edges: vec![],
        });

        self.visit_block(while_statement.block.as_ref());

        let loop_ctx = self.loop_stack.pop().unwrap();
        let break_edges = loop_ctx.break_edges;
        let continue_edges = loop_ctx.continue_edges;

        // Collect all edges targeting the header: body back-edge + continue edges
        let mut header_patches: Vec<(BlockId, ValueId, Vec<(usize, String, ValueId)>)> = vec![];
        if self.is_terminator_unreachable() {
            let body_end_block_id = self.current_block_id();
            let body_end_mem = self.cur_mem;
            let body_end_vars = self.snapshot_vars();
            let mem = self.new_value(Type::Mem, "");
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Br {
                mem,
                target: header_bb_id,
            };
            self.add_predecessor(header_bb_id, body_end_block_id);
            header_patches.push((body_end_block_id, body_end_mem, body_end_vars));
        }
        header_patches.extend(continue_edges);

        if !header_patches.is_empty() {
            self.patch_phis_from_edges(header_bb_id, mem_phi_result, &var_phis, &header_patches);
        }

        // Exit block: restore var_to_value_id to header phi results, then merge breaks
        for (scope_ind, var_name, phi_result) in &var_phis {
            self.var_to_value_id
                .get_mut(scope_ind)
                .unwrap()
                .insert(var_name.clone(), *phi_result);
        }
        self.start_block_with_id(exit_bb_id, "while_exit");

        if !break_edges.is_empty() {
            // Use cond_block_id/cond_mem/cond_vars for the normal exit path
            // (condition was false), since condition eval may have created
            // short-circuit blocks between header and the exit branch.
            let mut exit_incomings = vec![(cond_block_id, cond_mem, cond_vars)];
            exit_incomings.extend(break_edges);
            self.emit_merge_phis(&var_phis, &exit_incomings);
        } else {
            self.cur_mem = cond_mem;
        }
    }

    fn visit_return_statement(&mut self, return_statement: &AST::ReturnStatement) {
        if let Some(expr) = return_statement.expr.as_ref().as_ref() {
            self.visit_expression(expr);
            let ret_val = self.get_result_value_id();
            let mem = self.cur_mem;
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term = Terminator::Ret {
                mem,
                value: ret_val,
            };
        } else {
            let mem = self.cur_mem;
            self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term =
                Terminator::RetVoid { mem };
        }
    }

    fn visit_statement_control(&mut self, statement_control: &AST::StatementControl) {
        let from_block = self.current_block_id();
        let snap_mem = self.cur_mem;
        let var_snapshot = self.snapshot_vars();

        let loop_ctx = self.loop_stack.last().expect("break/continue outside loop");
        let (target, is_break) = match statement_control.op.as_str() {
            "break" => (loop_ctx.exit_block, true),
            "continue" => (loop_ctx.continue_target, false),
            _ => {
                eprintln!(
                    "Error: invalid statement control op: {}",
                    statement_control.op
                );
                panic!();
            }
        };

        let mem = self.new_value(Type::Mem, "");
        self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind].term =
            Terminator::Br { mem, target };
        self.add_predecessor(target, from_block);

        let edge = (from_block, snap_mem, var_snapshot);
        if is_break {
            self.loop_stack.last_mut().unwrap().break_edges.push(edge);
        } else {
            self.loop_stack
                .last_mut()
                .unwrap()
                .continue_edges
                .push(edge);
        }
    }

    fn visit_assignment(&mut self, assignment: &AST::Assignment) {
        let assign_op = assignment.assign_op.as_str();

        // Resolve the assignment target via visit_location
        // - Identifier (status 2): sets result_var_type, result_is_global
        // - IndexExpression (status 2): computes elem addr into result_value_id,
        //   sets result_var_type to elem type, result_is_global
        self.visit_location(assignment.assign_var.as_ref());
        let var_type = self.get_result_var_type();
        let is_global = self.get_is_global();

        // For IndexExpression assignments, save the elem_addr BEFORE evaluating RHS
        // because visit_expression will overwrite result_value_id
        let elem_addr_opt = match assignment.assign_var.as_ref() {
            AST::ASTNode::IndexExpression(_) => Some(self.get_result_value_id()),
            _ => None,
        };

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
                    let bin_op = compound_assign_to_binop(assign_op);
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
                    // For simple '=' assignments, propagate the variable name
                    // to the RHS value if it currently has a generic name.
                    if assign_op == "=" {
                        if let Some(info) =
                            self.cur_func.as_mut().unwrap().values.get_mut(&rhs_value)
                        {
                            if is_generic_value_name(&info.org_name) {
                                info.org_name = var_name.to_string();
                            }
                        }
                    }
                    self.var_to_value_id
                        .entry(var_scope_ind)
                        .or_insert_with(HashMap::new)
                        .insert(var_name.to_string(), rhs_value);
                }
            }

            // Array element assignment
            AST::ASTNode::IndexExpression(_) => {
                // Use the elem_addr we saved before evaluating the RHS
                let elem_addr =
                    elem_addr_opt.expect("elem_addr should be saved for IndexExpression");

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

                    let bin_op = compound_assign_to_binop(assign_op);
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
                    let mut bytes: Vec<i8> = process_string_literal(&string_constant.value);
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

    fn visit_int_cast(&mut self, int_cast: &AST::IntCast) {
        self.visit_expression(&int_cast.cast_expr);
        let src = self.get_result_value_id();
        let src_ty = self.cur_func.as_ref().unwrap().values[&src].ty.clone();

        let kind = match src_ty {
            Type::I32 => {
                // int(int) is a no-op
                self.set_result_value_id(src);
                return;
            }
            Type::I64 => CastKind::I64ToI32,
            _ => {
                eprintln!("Error: int() cast on non-numeric type");
                panic!();
            }
        };

        let result = self.new_value(Type::I32, "cast");
        self.emit_instr(vec![result], InstrKind::Cast { kind, src });
        self.set_result_value_id(result);
    }

    fn visit_long_cast(&mut self, long_cast: &AST::LongCast) {
        self.visit_expression(&long_cast.cast_expr);
        let src = self.get_result_value_id();
        let src_ty = self.cur_func.as_ref().unwrap().values[&src].ty.clone();

        let kind = match src_ty {
            Type::I64 => {
                // long(long) is a no-op
                self.set_result_value_id(src);
                return;
            }
            Type::I32 => CastKind::I32ToI64,
            _ => {
                eprintln!("Error: long() cast on non-numeric type");
                panic!();
            }
        };

        let result = self.new_value(Type::I64, "cast");
        self.emit_instr(vec![result], InstrKind::Cast { kind, src });
        self.set_result_value_id(result);
    }

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
                self.start_block_with_id(rhs_bb_id, "sc_rhs");
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
                    self.start_block_with_id(merge_bb, "sc_merge");

                    // Boolean result phi
                    let phi_result = self.new_value(Type::I1, "logic");
                    let phi_id = InstrId(self.get_next_instr_id());
                    self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
                        .phis
                        .push(Phi {
                            id: phi_id,
                            result: phi_result,
                            ty: Type::I1,
                            incomings: phi_incomings,
                        });
                    self.cur_func
                        .as_mut()
                        .unwrap()
                        .values
                        .get_mut(&phi_result)
                        .unwrap()
                        .declared_by = Some(phi_id);

                    // Memory phi to merge memory tokens from all paths
                    let mem_phi_result = self.new_value(Type::Mem, "");
                    let mem_phi_id = InstrId(self.get_next_instr_id());
                    self.cur_func.as_mut().unwrap().blocks[self.cur_block_ind]
                        .phis
                        .push(Phi {
                            id: mem_phi_id,
                            result: mem_phi_result,
                            ty: Type::Mem,
                            incomings: mem_phi_incomings,
                        });
                    self.cur_func
                        .as_mut()
                        .unwrap()
                        .values
                        .get_mut(&mem_phi_result)
                        .unwrap()
                        .declared_by = Some(mem_phi_id);
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
                    // put newly declared variable in FunctionIR values map
                    let new_value_id = self.new_value(self.result_var_type.clone(), id_name);

                    // if we are initializing a method then push the parameters as value ids
                    if self.init_method {
                        self.cur_func.as_mut().unwrap().params.push(new_value_id);
                    }

                    self.var_to_value_id
                        .entry(var_scope_ind)
                        .or_insert(HashMap::new())
                        .insert(id_name.to_string(), new_value_id);
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
            let parsed = int_constant.value.parse::<i64>().unwrap();
            int_value = if int_constant.is_neg {
                (-parsed) as i32
            } else {
                parsed as i32
            };
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
            let parsed = long_constant.value.parse::<i64>().unwrap();
            long_value = if long_constant.is_neg {
                -parsed
            } else {
                parsed
            };
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

pub fn compile_to_ssa_cfg(ast: AST::Program, symbol_table: SymbolTable) -> SSA_CFG_Compiler {
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
        next_instr_id: 0,

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

    return ssa_cfg_compiler;
}
