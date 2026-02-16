use std::collections::HashMap;

use super::super::cfg::three_address_code::{
    BasicBlock, BinOp, BlockId, CastKind, ConstValue, FunctionIR, GlobalDecl, GlobalKind, ICmpPred,
    Instr, InstrKind, ProgramIR, Symbol, Terminator, Type, UnOp, ValueId,
};

// ==================== Location Tracking ====================

/// Where a ValueId lives at runtime
#[derive(Clone, Debug)]
pub enum Location {
    /// Stack slot at -offset(%rbp)
    Stack(i32),
    /// A compile-time constant (no storage needed, can emit as immediate)
    Immediate(ConstValue),
}

// ==================== Code Generator ====================

pub struct CodeGenerator {
    /// Accumulated assembly output lines
    output: Vec<String>,

    // ---- per-program state ----
    /// Map from array symbol name to its compile-time length (populated during data section emission)
    array_lengths: HashMap<String, u32>,

    // ---- per-function state (reset for each function) ----
    /// Map from ValueId to its runtime location
    value_locations: HashMap<ValueId, Location>,
    /// Next available stack offset (grows downward from rbp)
    next_stack_offset: i32,
    /// Total stack frame size for current function (set after allocation)
    frame_size: i32,
}

impl CodeGenerator {
    pub fn new() -> Self {
        CodeGenerator {
            output: Vec::new(),
            array_lengths: HashMap::new(),
            value_locations: HashMap::new(),
            next_stack_offset: 0,
            frame_size: 0,
        }
    }

    /// Top-level entry point: generate assembly for the entire program
    pub fn generate(&mut self, program: &ProgramIR) -> String {
        self.emit_data_section(program);
        self.emit_text_section(program);
        self.output.join("\n")
    }

    // ==================== Assembly Emission Helpers ====================

    /// Emit a raw line of assembly
    fn emit(&mut self, line: &str) {
        self.output.push(line.to_string());
    }

    /// Emit a label (no indentation)
    fn emit_label(&mut self, label: &str) {
        self.output.push(format!("{}:", label));
    }

    /// Emit an indented instruction
    fn emit_instr(&mut self, instr: &str) {
        self.output.push(format!("    {}", instr));
    }

    /// Emit a blank line for readability
    fn emit_blank(&mut self) {
        self.output.push(String::new());
    }

    /// Emit a comment
    fn emit_comment(&mut self, comment: &str) {
        self.output.push(format!("    # {}", comment));
    }

    // ==================== Top-Level Sections ====================

    /// Emit the .data section for global variables and string literals
    fn emit_data_section(&mut self, program: &ProgramIR) {
        self.emit(".section .data");
        for global in &program.globals {
            self.emit_global_decl(global);
        }
        self.emit_blank();
    }

    /// Emit a single global declaration
    fn emit_global_decl(&mut self, global: &GlobalDecl) {
        let label = &global.sym.0;
        match &global.kind {
            GlobalKind::GlobalStr { bytes } => {
                self.emit_label(label);
                let byte_strs: Vec<String> =
                    bytes.iter().map(|b| format!("{}", *b as u8)).collect();
                self.emit_instr(&format!(".byte {}", byte_strs.join(", ")));
            }
            GlobalKind::GlobalScalar { ty, init } => {
                self.emit_label(label);
                let directive = self.data_directive(ty);
                match init {
                    Some(cv) => {
                        self.emit_instr(&format!("{} {}", directive, self.const_value_int(cv)))
                    }
                    None => self.emit_instr(&format!("{} 0", directive)),
                }
            }
            GlobalKind::GlobalArray { elem_ty, len, init } => {
                self.array_lengths.insert(label.to_string(), *len);
                self.emit_label(label);
                match init {
                    Some(values) => {
                        let directive = self.data_directive(elem_ty);
                        for cv in values {
                            self.emit_instr(&format!("{} {}", directive, self.const_value_int(cv)));
                        }
                    }
                    None => {
                        let total_bytes = *len as i32 * self.type_size(elem_ty);
                        self.emit_instr(&format!(".zero {}", total_bytes));
                    }
                }
            }
        }
    }

    /// Return the appropriate data directive for a type (.long for 32-bit, .quad for 64-bit)
    fn data_directive(&self, ty: &Type) -> &'static str {
        match ty {
            Type::I1 | Type::I8 | Type::I32 => ".long",
            Type::I64 | Type::Ptr(_) => ".quad",
            _ => ".long",
        }
    }

    /// Extract the integer value from a ConstValue
    fn const_value_int(&self, cv: &ConstValue) -> i64 {
        match cv {
            ConstValue::I1(b) => *b as i64,
            ConstValue::I32(n) => *n as i64,
            ConstValue::I64(n) => *n,
        }
    }

    /// Emit the .text section with all function definitions
    fn emit_text_section(&mut self, program: &ProgramIR) {
        self.emit(".section .text");
        self.emit_blank();

        for (name, func) in &program.functions {
            self.generate_function(name, func);
        }
    }

    // ==================== Function Generation ====================

    /// Generate assembly for a single function
    fn generate_function(&mut self, name: &str, func: &FunctionIR) {
        // Reset per-function state
        self.value_locations.clear();
        self.next_stack_offset = 0;
        self.frame_size = 0;

        // Phase 1: Allocate stack slots for all ValueIds
        self.allocate_values(func);

        // Phase 2: Emit function label and prologue
        self.emit_function_header(name);
        self.emit_prologue();

        // Phase 3: Move parameters from argument registers to their stack slots
        self.emit_param_moves(func);

        // Phase 4: Emit each basic block
        for block in &func.blocks {
            self.emit_block(name, block, func);
        }

        self.emit_blank();
    }

    // ==================== Value Allocation (Stack-Only, Phase 1) ====================

    /// Allocate a stack slot for every ValueId in the function.
    /// Skips Mem and Void typed values (they don't need storage).
    fn allocate_values(&mut self, func: &FunctionIR) {
        for (vid, info) in &func.values {
            match &info.ty {
                // Mem tokens and Void don't need storage
                Type::Mem | Type::Void | Type::None => continue,
                ty => {
                    let size = self.type_size(ty);
                    self.next_stack_offset += size;
                    self.value_locations
                        .insert(*vid, Location::Stack(self.next_stack_offset));
                }
            }
        }

        // Align frame size to 16 bytes
        self.frame_size = (self.next_stack_offset + 15) & !15;
    }

    /// Return the size in bytes for a given IR type
    fn type_size(&self, ty: &Type) -> i32 {
        match ty {
            Type::I1 => 4, // store bools as 4 bytes for alignment
            Type::I8 => 4, // pad to 4 bytes for alignment
            Type::I32 => 4,
            Type::I64 => 8,
            Type::Ptr(_) => 8,
            _ => 0,
        }
    }

    /// Return the AT&T operand string for accessing a ValueId's location (e.g., "-8(%rbp)")
    fn value_operand(&self, vid: ValueId) -> String {
        match self.value_locations.get(&vid) {
            Some(Location::Stack(offset)) => format!("-{}(%rbp)", offset),
            Some(Location::Immediate(cv)) => match cv {
                ConstValue::I1(b) => format!("${}", *b as i32),
                ConstValue::I32(n) => format!("${}", n),
                ConstValue::I64(n) => format!("${}", n),
            },
            None => panic!("ValueId {:?} has no allocated location", vid),
        }
    }

    /// Return the AT&T instruction suffix for a type ("l" for 32-bit, "q" for 64-bit)
    fn type_suffix(&self, ty: &Type) -> &'static str {
        match ty {
            Type::I1 | Type::I8 | Type::I32 => "l",
            Type::I64 | Type::Ptr(_) => "q",
            _ => "l",
        }
    }

    // ==================== Prologue / Epilogue ====================

    /// Emit the function header (.globl directive and label)
    fn emit_function_header(&mut self, name: &str) {
        self.emit(&format!(".globl {}", name));
        self.emit_label(name);
    }

    /// Emit function prologue: save rbp, set up frame, allocate stack space
    fn emit_prologue(&mut self) {
        self.emit_instr("pushq %rbp");
        self.emit_instr("movq %rsp, %rbp");
        if self.frame_size > 0 {
            self.emit_instr(&format!("subq ${}, %rsp", self.frame_size));
        }
    }

    /// Emit function epilogue: restore rsp/rbp, return
    fn emit_epilogue(&mut self) {
        self.emit_instr("movq %rbp, %rsp");
        self.emit_instr("popq %rbp");
        self.emit_instr("ret");
    }

    /// Move function parameters from argument registers into their stack slots
    fn emit_param_moves(&mut self, func: &FunctionIR) {
        let arg_regs_64 = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];
        let arg_regs_32 = ["%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"];

        for (i, param_vid) in func.params.iter().enumerate() {
            if i >= 6 {
                // TODO: handle stack-passed arguments (7th+)
                todo!("stack-passed parameter {}", i);
            }

            let param_ty = &func.values[param_vid].ty;
            let (reg, suffix) = match param_ty {
                Type::I64 | Type::Ptr(_) => (arg_regs_64[i], "q"),
                _ => (arg_regs_32[i], "l"),
            };
            let dest = self.value_operand(*param_vid);
            self.emit_instr(&format!("mov{} {}, {}", suffix, reg, dest));
        }
    }

    // ==================== Basic Block Emission ====================

    /// Emit a complete basic block: label, phis, instructions, terminator
    fn emit_block(&mut self, func_name: &str, block: &BasicBlock, func: &FunctionIR) {
        // Block label
        self.emit_label(&self.block_label(func_name, block.id));

        // Phi nodes (handled by predecessor copies -- see emit_phi_copies)
        // Nothing emitted here; phi resolution happens at predecessor block ends

        // Instructions
        for instr in &block.instrs {
            self.emit_instruction(instr, func);
        }

        // Terminator
        self.emit_terminator(func_name, &block.term, func);
    }

    /// Generate a label string for a block
    fn block_label(&self, func_name: &str, block_id: BlockId) -> String {
        format!(".{}_bb{}", func_name, block_id.0)
    }

    // ==================== Instruction Emission ====================

    /// Emit assembly for a single IR instruction
    fn emit_instruction(&mut self, instr: &Instr, _func: &FunctionIR) {
        match &instr.kind {
            InstrKind::Const(cv) => {
                self.emit_const(instr, cv);
            }
            InstrKind::BinOp { op, ty, lhs, rhs } => {
                self.emit_binop(instr, *op, ty, *lhs, *rhs);
            }
            InstrKind::UnOp { op, ty, arg } => {
                self.emit_unop(instr, *op, ty, *arg);
            }
            InstrKind::ICmp { pred, ty, lhs, rhs } => {
                self.emit_icmp(instr, *pred, ty, *lhs, *rhs);
            }
            InstrKind::Cast { kind, src } => {
                self.emit_cast(instr, *kind, *src);
            }
            InstrKind::GlobalAddr { sym, ty } => {
                self.emit_global_addr(instr, sym, ty);
            }
            InstrKind::GlobalArrayAddr { sym, elem_ty } => {
                self.emit_global_array_addr(instr, sym, elem_ty);
            }
            InstrKind::GlobalStrAddr { sym } => {
                self.emit_global_str_addr(instr, sym);
            }
            InstrKind::ElemAddr {
                elem_ty,
                base,
                index,
            } => {
                self.emit_elem_addr(instr, elem_ty, *base, *index);
            }
            InstrKind::Len { sym } => {
                self.emit_len(instr, sym);
            }
            InstrKind::Load { ty, mem: _, addr } => {
                self.emit_load(instr, ty, *addr);
            }
            InstrKind::Store {
                ty,
                mem: _,
                addr,
                value,
            } => {
                self.emit_store(instr, ty, *addr, *value);
            }
            InstrKind::Call {
                mem: _,
                callee,
                args,
                ret_ty,
            } => {
                self.emit_call(instr, callee, args, ret_ty, false);
            }
            InstrKind::CallImport {
                mem: _,
                callee,
                args,
                ret_ty,
            } => {
                self.emit_call(instr, callee, args, ret_ty, true);
            }
        }
    }

    // ---- Individual instruction emitters ----

    fn emit_const(&mut self, instr: &Instr, cv: &ConstValue) {
        // Get the destination location (stack slot)
        let result = instr.results[0];
        let dest = self.value_operand(result);

        // Determine instruction suffix based on constant type
        let (suffix, imm) = match cv {
            ConstValue::I1(b) => ("l", *b as i64),
            ConstValue::I32(n) => ("l", *n as i64),
            ConstValue::I64(n) => ("q", *n),
        };

        // Emit: movl/movq $imm, -offset(%rbp)
        self.emit_instr(&format!("mov{} ${}, {}", suffix, imm, dest));
    }

    fn emit_binop(&mut self, instr: &Instr, op: BinOp, ty: &Type, lhs: ValueId, rhs: ValueId) {
        let suffix = self.type_suffix(ty);
        let reg = if suffix == "l" { "%eax" } else { "%rax" };

        let lhs_op = self.value_operand(lhs);
        let rhs_op = self.value_operand(rhs);
        let result = instr.results[0];
        let dest = self.value_operand(result);

        // Load lhs into register
        self.emit_instr(&format!("mov{} {}, {}", suffix, lhs_op, reg));

        // Perform operation with rhs
        match op {
            BinOp::Add => {
                // addl rhs, %eax
                self.emit_instr(&format!("add{} {}, {}", suffix, rhs_op, reg));
            }
            BinOp::Sub => {
                // subl rhs, %eax
                self.emit_instr(&format!("sub{} {}, {}", suffix, rhs_op, reg));
            }
            BinOp::Mul => {
                // imull rhs, %eax (signed multiply)
                self.emit_instr(&format!("imul{} {}, {}", suffix, rhs_op, reg));
            }
            BinOp::SDiv | BinOp::SRem => {
                // Division and remainder are more complex - defer to Phase 6
                todo!("emit_binop: div/rem not yet implemented (Phase 6)");
            }
        }

        // Store result
        self.emit_instr(&format!("mov{} {}, {}", suffix, reg, dest));
    }

    fn emit_unop(&mut self, instr: &Instr, op: UnOp, ty: &Type, arg: ValueId) {
        let suffix = self.type_suffix(ty);
        let reg = if suffix == "l" { "%eax" } else { "%rax" };

        let arg_op = self.value_operand(arg);
        let result = instr.results[0];
        let dest = self.value_operand(result);

        // Load arg into register
        self.emit_instr(&format!("mov{} {}, {}", suffix, arg_op, reg));

        // Perform operation
        match op {
            UnOp::Neg => {
                // negl %eax (arithmetic negation)
                self.emit_instr(&format!("neg{} {}", suffix, reg));
            }
            UnOp::Not => {
                // Boolean NOT: xor with 1 (flips 0<->1)
                // Use 32-bit operation for bools
                self.emit_instr("xorl $1, %eax");
            }
        }

        // Store result
        self.emit_instr(&format!("mov{} {}, {}", suffix, reg, dest));
    }

    fn emit_icmp(
        &mut self,
        instr: &Instr,
        pred: ICmpPred,
        ty: &Type,
        lhs: ValueId,
        rhs: ValueId,
    ) {
        let suffix = self.type_suffix(ty);
        let reg = if suffix == "l" { "%eax" } else { "%rax" };

        let lhs_op = self.value_operand(lhs);
        let rhs_op = self.value_operand(rhs);
        let result = instr.results[0];
        let dest = self.value_operand(result);

        // Load lhs into register
        self.emit_instr(&format!("mov{} {}, {}", suffix, lhs_op, reg));

        // Compare with rhs (AT&T syntax: cmpl rhs, lhs)
        self.emit_instr(&format!("cmp{} {}, {}", suffix, rhs_op, reg));

        // Set byte based on condition code
        let setcc = match pred {
            ICmpPred::Eq => "sete",   // set if equal
            ICmpPred::Ne => "setne",  // set if not equal
            ICmpPred::Lt => "setl",   // set if less (signed)
            ICmpPred::Le => "setle",  // set if less or equal (signed)
            ICmpPred::Gt => "setg",   // set if greater (signed)
            ICmpPred::Ge => "setge",  // set if greater or equal (signed)
        };
        self.emit_instr(&format!("{} %al", setcc));

        // Zero-extend byte to 32-bit (result is i1/bool, stored as 32-bit)
        self.emit_instr("movzbl %al, %eax");

        // Store result (always 32-bit for bools)
        self.emit_instr(&format!("movl %eax, {}", dest));
    }

    fn emit_cast(&mut self, _instr: &Instr, _kind: CastKind, _src: ValueId) {
        // TODO: movslq -off(%rbp), %rax (i32->i64) or movl %eax, %eax (i64->i32 truncate)
        todo!("emit_cast");
    }

    fn emit_global_addr(&mut self, _instr: &Instr, _sym: &Symbol, _ty: &Type) {
        // TODO: leaq sym(%rip), %rax; movq %rax, -off(%rbp)
        todo!("emit_global_addr");
    }

    fn emit_global_array_addr(&mut self, _instr: &Instr, _sym: &Symbol, _elem_ty: &Type) {
        // TODO: leaq sym(%rip), %rax; movq %rax, -off(%rbp)
        todo!("emit_global_array_addr");
    }

    fn emit_global_str_addr(&mut self, _instr: &Instr, _sym: &Symbol) {
        // TODO: leaq sym(%rip), %rax; movq %rax, -off(%rbp)
        todo!("emit_global_str_addr");
    }

    fn emit_elem_addr(&mut self, _instr: &Instr, _elem_ty: &Type, _base: ValueId, _index: ValueId) {
        // TODO: movq -off(%rbp), %rax; movslq -off(%rbp), %rcx; leaq (%rax,%rcx,4), %rax; movq %rax, -off(%rbp)
        todo!("emit_elem_addr");
    }

    fn emit_len(&mut self, _instr: &Instr, _sym: &Symbol) {
        // TODO: movl $<compile-time-length>, -off(%rbp)
        todo!("emit_len");
    }

    fn emit_load(&mut self, _instr: &Instr, _ty: &Type, _addr: ValueId) {
        // TODO: movq -off(%rbp), %rax; movl (%rax), %ecx; movl %ecx, -off(%rbp)
        todo!("emit_load");
    }

    fn emit_store(&mut self, _instr: &Instr, _ty: &Type, _addr: ValueId, _value: ValueId) {
        // TODO: movq -off(%rbp), %rax; movl -off(%rbp), %ecx; movl %ecx, (%rax)
        todo!("emit_store");
    }

    fn emit_call(
        &mut self,
        _instr: &Instr,
        _callee: &Symbol,
        _args: &[ValueId],
        _ret_ty: &Type,
        _is_import: bool,
    ) {
        // TODO:
        // 1. Move args into %rdi, %rsi, %rdx, %rcx, %r8, %r9 (or pushq for 7th+)
        // 2. Ensure 16-byte stack alignment before call
        // 3. call <callee>
        // 4. movl %eax, -off(%rbp)  (if non-void)
        todo!("emit_call");
    }

    // ==================== Terminator Emission ====================

    fn emit_terminator(&mut self, func_name: &str, term: &Terminator, _func: &FunctionIR) {
        match term {
            Terminator::Br { target, .. } => {
                self.emit_instr(&format!("jmp {}", self.block_label(func_name, *target)));
            }
            Terminator::CBr {
                cond: _,
                then_bb: _,
                else_bb: _,
                ..
            } => {
                // TODO: movl -off(%rbp), %eax; testl %eax, %eax; jne .L_then; jmp .L_else
                todo!("emit CBr terminator");
            }
            Terminator::Ret { value: _, .. } => {
                // TODO: movl -off(%rbp), %eax; epilogue; ret
                todo!("emit Ret terminator");
            }
            Terminator::RetVoid { .. } => {
                self.emit_epilogue();
            }
            Terminator::Unreachable => {
                // Should not be reached in well-formed IR
                self.emit_comment("unreachable");
            }
        }
    }

    // ==================== Phi Resolution ====================

    /// Emit copies for phi resolution at the end of a predecessor block.
    /// Called before the terminator jump to patch phi incomings in the successor.
    fn emit_phi_copies(
        &mut self,
        _from_block: BlockId,
        _to_block: &BasicBlock,
        _func: &FunctionIR,
    ) {
        // TODO: for each phi in to_block, find the incoming for from_block,
        // load the incoming value into a register, store it to the phi result's location
        // e.g. movl -off(%rbp), %eax; movl %eax, -off(%rbp)
        todo!("emit_phi_copies");
    }
}
