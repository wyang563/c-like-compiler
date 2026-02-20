use std::collections::HashMap;

use super::super::cfg::three_address_code::{
    BasicBlock, BinOp, BlockId, CastKind, ConstValue, FunctionIR, GlobalDecl, GlobalKind, ICmpPred,
    Instr, InstrKind, ProgramIR, Symbol, Terminator, Type, UnOp, ValueId,
};

use super::reg_alloc::RegAlloc;

pub struct CodeGenerator {
    program_alloc: HashMap<String, RegAlloc>,
}

impl CodeGenerator {
    pub fn new(program_alloc: HashMap<String, RegAlloc>) -> Self {
        CodeGenerator {
            program_alloc: program_alloc,
        }
    }

    pub fn generate(&mut self, _ssa_cfg: &ProgramIR) -> String {
        // Placeholder for actual code generation logic
        "// Assembly code output goes here".to_string()
    }
}
