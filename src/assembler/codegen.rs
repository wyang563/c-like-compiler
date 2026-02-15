use std::collections::HashMap;

use super::super::cfg::three_address_code::{
    BasicBlock, BinOp, BlockId, CastKind, ConstValue, FunctionIR, GlobalDecl, GlobalKind, ICmpPred,
    Instr, InstrKind, Phi, ProgramIR, Symbol, Terminator, Type, UnOp, ValueId,
};

// ==================== Location Tracking ====================

/// Where a ValueId lives at runtime
#[derive(Clone, Debug)]
pub enum Location {
    /// Stack slot at [rbp - offset]
    Stack(i32),
    /// A compile-time constant (no storage needed, can emit as immediate)
    Immediate(ConstValue),
}

// ==================== Code Generator ====================

pub struct CodeGenerator {
    /// Accumulated assembly output lines
    output: Vec<String>,

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
            value_locations: HashMap::new(),
            next_stack_offset: 0,
            frame_size: 0,
        }
    }

    /// Top-level entry point: generate assembly for the entire program
    pub fn generate(&mut self, program: &ProgramIR) -> String {
        self.emit_prelude();
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
        self.output.push(format!("    ; {}", comment));
    }

    // ==================== Top-Level Sections ====================

    /// Emit assembler directives at the top of the file
    fn emit_prelude(&mut self) {
        self.emit(".intel_syntax noprefix");
        self.emit_blank();
    }

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
                // TODO: emit string bytes as .byte directives
                todo!("emit GlobalStr for {}", label);
            }
            GlobalKind::GlobalScalar { ty, init } => {
                // TODO: emit scalar with .long/.quad and optional init value
                todo!("emit GlobalScalar for {}", label);
            }
            GlobalKind::GlobalArray { elem_ty, len, init } => {
                // TODO: emit array with repeated .long/.quad entries or .zero
                todo!("emit GlobalArray for {}", label);
            }
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
                    let size = Self::type_size(ty);
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
    fn type_size(ty: &Type) -> i32 {
        match ty {
            Type::I1 => 4, // store bools as 4 bytes for alignment
            Type::I8 => 4, // pad to 4 bytes for alignment
            Type::I32 => 4,
            Type::I64 => 8,
            Type::Ptr(_) => 8,
            _ => 0,
        }
    }

    /// Return the operand string for accessing a ValueId's location (e.g., "[rbp-8]")
    fn value_operand(&self, vid: ValueId) -> String {
        match self.value_locations.get(&vid) {
            Some(Location::Stack(offset)) => format!("[rbp-{}]", offset),
            Some(Location::Immediate(cv)) => match cv {
                ConstValue::I1(b) => format!("{}", *b as i32),
                ConstValue::I32(n) => format!("{}", n),
                ConstValue::I64(n) => format!("{}", n),
            },
            None => panic!("ValueId {:?} has no allocated location", vid),
        }
    }

    /// Return the size qualifier for a type ("dword" for 32-bit, "qword" for 64-bit)
    fn size_qualifier(ty: &Type) -> &'static str {
        match ty {
            Type::I1 | Type::I8 | Type::I32 => "dword",
            Type::I64 | Type::Ptr(_) => "qword",
            _ => "dword",
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
        self.emit_instr("push rbp");
        self.emit_instr("mov rbp, rsp");
        if self.frame_size > 0 {
            self.emit_instr(&format!("sub rsp, {}", self.frame_size));
        }
    }

    /// Emit function epilogue: restore rsp/rbp, return
    fn emit_epilogue(&mut self) {
        self.emit_instr("mov rsp, rbp");
        self.emit_instr("pop rbp");
        self.emit_instr("ret");
    }

    /// Move function parameters from argument registers into their stack slots
    fn emit_param_moves(&mut self, func: &FunctionIR) {
        let arg_regs_64 = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];
        let arg_regs_32 = ["edi", "esi", "edx", "ecx", "r8d", "r9d"];

        for (i, param_vid) in func.params.iter().enumerate() {
            if i >= 6 {
                // TODO: handle stack-passed arguments (7th+)
                todo!("stack-passed parameter {}", i);
            }

            let param_ty = &func.values[param_vid].ty;
            let reg = match param_ty {
                Type::I64 | Type::Ptr(_) => arg_regs_64[i],
                _ => arg_regs_32[i],
            };
            let dest = self.value_operand(*param_vid);
            let qual = Self::size_qualifier(param_ty);
            self.emit_instr(&format!("mov {} {}, {}", qual, dest, reg));
        }
    }

    // ==================== Basic Block Emission ====================

    /// Emit a complete basic block: label, phis, instructions, terminator
    fn emit_block(&mut self, func_name: &str, block: &BasicBlock, func: &FunctionIR) {
        // Block label
        self.emit_label(&Self::block_label(func_name, block.id));

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
    fn block_label(func_name: &str, block_id: BlockId) -> String {
        format!(".L_{}_bb{}", func_name, block_id.0)
    }

    // ==================== Instruction Emission ====================

    /// Emit assembly for a single IR instruction
    fn emit_instruction(&mut self, instr: &Instr, func: &FunctionIR) {
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
            InstrKind::Load { ty, mem, addr } => {
                self.emit_load(instr, ty, *addr);
            }
            InstrKind::Store {
                ty,
                mem,
                addr,
                value,
            } => {
                self.emit_store(instr, ty, *addr, *value);
            }
            InstrKind::Call {
                mem,
                callee,
                args,
                ret_ty,
            } => {
                self.emit_call(instr, callee, args, ret_ty, false);
            }
            InstrKind::CallImport {
                mem,
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
        // TODO: mov immediate value into result's stack slot
        todo!("emit_const");
    }

    fn emit_binop(&mut self, instr: &Instr, op: BinOp, ty: &Type, lhs: ValueId, rhs: ValueId) {
        // TODO: load lhs into eax/rax, perform op with rhs, store result
        // NOTE: idiv is special -- needs cdq/cqo setup, result in rax (quot) or rdx (rem)
        todo!("emit_binop");
    }

    fn emit_unop(&mut self, instr: &Instr, op: UnOp, ty: &Type, arg: ValueId) {
        // TODO: load arg, apply neg/not, store result
        todo!("emit_unop");
    }

    fn emit_icmp(&mut self, instr: &Instr, pred: ICmpPred, ty: &Type, lhs: ValueId, rhs: ValueId) {
        // TODO: cmp lhs, rhs; setcc al; movzx eax, al; store result
        todo!("emit_icmp");
    }

    fn emit_cast(&mut self, instr: &Instr, kind: CastKind, src: ValueId) {
        // TODO: movsx (i32->i64) or truncate (i64->i32)
        todo!("emit_cast");
    }

    fn emit_global_addr(&mut self, instr: &Instr, sym: &Symbol, ty: &Type) {
        // TODO: lea rax, [rip + sym]; store rax to result slot
        todo!("emit_global_addr");
    }

    fn emit_global_array_addr(&mut self, instr: &Instr, sym: &Symbol, elem_ty: &Type) {
        // TODO: lea rax, [rip + sym]; store rax to result slot
        todo!("emit_global_array_addr");
    }

    fn emit_global_str_addr(&mut self, instr: &Instr, sym: &Symbol) {
        // TODO: lea rax, [rip + sym]; store rax to result slot
        todo!("emit_global_str_addr");
    }

    fn emit_elem_addr(&mut self, instr: &Instr, elem_ty: &Type, base: ValueId, index: ValueId) {
        // TODO: load base ptr, load index, lea rax [base + index*scale], store result
        todo!("emit_elem_addr");
    }

    fn emit_len(&mut self, instr: &Instr, sym: &Symbol) {
        // TODO: emit compile-time constant array length as immediate mov
        todo!("emit_len");
    }

    fn emit_load(&mut self, instr: &Instr, ty: &Type, addr: ValueId) {
        // TODO: load addr from stack, mov value from [addr], store to result slot
        todo!("emit_load");
    }

    fn emit_store(&mut self, instr: &Instr, ty: &Type, addr: ValueId, value: ValueId) {
        // TODO: load addr and value, mov [addr], value
        todo!("emit_store");
    }

    fn emit_call(
        &mut self,
        instr: &Instr,
        callee: &Symbol,
        args: &[ValueId],
        ret_ty: &Type,
        is_import: bool,
    ) {
        // TODO:
        // 1. Move args into rdi, rsi, rdx, rcx, r8, r9 (or push for 7th+)
        // 2. Ensure 16-byte stack alignment before call
        // 3. call <callee>
        // 4. Store rax to result slot (if non-void)
        todo!("emit_call");
    }

    // ==================== Terminator Emission ====================

    fn emit_terminator(&mut self, func_name: &str, term: &Terminator, func: &FunctionIR) {
        match term {
            Terminator::Br { target, .. } => {
                self.emit_instr(&format!("jmp {}", Self::block_label(func_name, *target)));
            }
            Terminator::CBr {
                cond,
                then_bb,
                else_bb,
                ..
            } => {
                // TODO: test cond, jne then_label, jmp else_label
                todo!("emit CBr terminator");
            }
            Terminator::Ret { value, .. } => {
                // TODO: mov rax, value; epilogue; ret
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
        // load the incoming value, store it to the phi result's location
        todo!("emit_phi_copies");
    }
}
