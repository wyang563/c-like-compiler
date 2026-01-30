// TAC instruction definitions

use std::collections::HashMap;

// IDs
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueId(pub u32);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

// Types
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    I1,
    I32,
    I64,
    Ptr(Box<Type>),
    Mem,
    Void,
    None,
}

// Symbols
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Symbol(pub String);

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol(s.to_string())
    }
}

// Program Structure/IR
#[derive(Clone, Debug)]
pub struct ProgramIR {
    pub globals: Vec<GlobalDecl>,
    pub functions: HashMap<String, FunctionIR>
}

#[derive(Clone, Debug)]
pub struct GlobalDecl {
    pub sym: Symbol,
    pub kind: GlobalKind,
}

/// Global "definitions" (these are not per-block instructions; they live at program scope).
#[derive(Clone, Debug)]
pub enum GlobalKind {
    GlobalStr { bytes: Vec<i8> },
    GlobalScalar { ty: Type, init: Option<ConstValue> },
    GlobalArray { elem_ty: Type, len: u32, init: Option<Vec<ConstValue>> },
}

#[derive(Clone, Debug)]
pub struct FunctionIR {
    pub name: Symbol,
    pub params: Vec<ValueId>,
    pub ret_ty: Type,
    pub values: HashMap<ValueId, ValueInfo>,
    pub blocks: Vec<BasicBlock>,
    pub block_id_to_ind: HashMap<BlockId, usize>,
    pub blocks_map: HashMap<BlockId, Vec<BlockId>>,
}

#[derive(Clone, Debug)]
pub struct ValueInfo {
    pub ty: Type,
    pub declared_location: Option<InstrLocation>,
    pub use_chain: Vec<InstrLocation>,
    pub org_name: String, // original var name in program
    pub debug_name: String // debug name for debugging
}

#[derive(Clone, Debug)]
pub struct BasicBlock {
    // id of this block inside function
    pub id: BlockId,
    // join blocks to determine mem_in value
    pub mem_in: Option<Phi>,
    // value phis only (non-mem variables)
    pub phis: Vec<Phi>,
    pub instrs: Vec<Instr>,
    pub term: Terminator,
}

#[derive(Clone, Debug)]
pub struct Phi {
    pub result: ValueId,
    pub ty: Type,
    pub incomings: Vec<(BlockId, ValueId)> // incoming block id edges into this Phi Node
}

// Instructions
#[derive(Clone, Debug)]
pub struct Instr {
    pub results: Vec<ValueId>,
    pub kind: InstrKind,
}

#[derive(Clone, Debug)]
pub struct InstrLocation {
    pub func: String, // func name as a string
    pub bb_ind: usize, // index of basic block in FunctionIR 
    pub instr_ind: usize // index of instruction in basic block instruction list
}

#[derive(Clone, Debug)]
pub enum InstrKind {
    // Returns a constant value of type bool, i32, or i64. 
    // %v:i32 = const_i32 42
    Const(ConstValue),

    // Returns a copy of a source value
    // %v4:i32 = copy %v1
    Copy { src: ValueId },

    // Binary op for input registers lhs, rhs with type ty and operation op
    // %v3:i32 = add_i32 %v1, %v2
    BinOp { op: BinOp, ty: Type, lhs: ValueId, rhs: ValueId },

    // Unary op for arg with type ty and operation op
    // %v2:i32 = neg_i32 %v1, %v3:i1 = not_i1 %v0
    UnOp { op: UnOp, ty: Type, arg: ValueId },

    // int comparison operation for predicate pred, args lhs and rhs with type ty
    // returns one SSA value of type i1
    // %v3:i1 = icmp_eq_i32 %v1, %v
    ICmp { pred: ICmpPred, ty: Type, lhs: ValueId, rhs: ValueId },

    // Casts src to another type according to the CastKind returning a value implied by kind
    // %v2:i64 = cast_i32_to_i64 %v1
    Cast { kind: CastKind, src: ValueId },

    // Address of a global scalar slot with type ty, returning ptr<ty>. Used for loading a global variable ie "global int x = 16"
    // %px:ptr<i32> = global_addr @gvar
    // %mem1, %x:i32 = load i32, %mem0, %px 
    GlobalAddr { sym: Symbol, ty: Type },

    // Address of first element in global array with type ty returning ptr<ty>.
    // %base:ptr<i32> = global_array_addr  @global_array : i32
    GlobalArrayAddr { sym: Symbol, elem_ty: Type },

    // Address of string literal global, returning ptr<i8>.
    // %p:ptr<i8> = global_str_addr @str0
    GlobalStrAddr { sym: Symbol },

    // Compute address of base[index] (base must be ptr<T>, index is i32).
    // %p:ptr<i32> = elem_addr i32, %base, %index
    ElemAddr { elem_ty: Type, base: ValueId, index: ValueId },

    // Load element from memory at addr where the value being loaded has type ty. Returns mem_out for sequencing and value of type ty.
    // %mem1, %x:i32 = load i32, %mem0, %addr
    Load { ty: Type, mem: ValueId, addr: ValueId },

    // Store element to memory at addr where the value being stored has type ty stored at addr ptr<ty>. Returns mem_out for sequencing.
    // %mem1:mem = store i32, %mem0, %addr, %v
    Store { ty: Type, mem: ValueId, addr: ValueId, value: ValueId },

    // Calls an internal non-imported function. callee is a symbol that exists in a program's function table mapping to the function being called.
    // results:
    // - if ret_ty == void: [mem_out]
    // - else: [mem_out, ret]
    Call { mem: ValueId, callee: Symbol, args: Vec<ValueId>, ret_ty: Type },

    /// Same as Call, but explicitly marks "import" calls (per Decaf spec).
    /// Typically returns i32 (per spec) and may accept string literals / arrays.
    CallImport { mem: ValueId, callee: Symbol, args: Vec<ValueId>, ret_ty: Type },
}

#[derive(Clone, Debug)]
pub enum ConstValue {
    I1(bool),
    I32(i32),
    I64(i64),
}

#[derive(Copy, Clone, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    SDiv,
    SRem,
}

#[derive(Copy, Clone, Debug)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Copy, Clone, Debug)]
pub enum ICmpPred {
    Eq,
    Ne,
    Lt, 
    Le,
    Gt,
    Ge,
}

#[derive(Copy, Clone, Debug)]
pub enum CastKind {
    I32ToI64,
    I64ToI32,
    I1ToI32,
    I1ToI64,
}

// -----------------------------
// Terminators
// -----------------------------

#[derive(Clone, Debug)]
pub enum Terminator {
    Br  { mem: ValueId, target: BlockId },
    CBr { mem: ValueId, cond: ValueId, then_bb: BlockId, else_bb: BlockId },
    RetVoid { mem: ValueId },
    Ret { mem: ValueId, value: ValueId },
    Unreachable,
}
