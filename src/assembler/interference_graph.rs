// Interference graph for register allocation.
//
// Nodes are either virtual (a ValueId) or pre-colored (a physical register).
// An undirected edge (u, v) means u and v must reside in different registers.
//
// Construction rules:
//   1. For every instruction i that defines d:
//        add edge (d, v) for every v ∈ live_after[i], v ≠ d.
//   2. Copy exception: for Assign{src→dst}, skip the (dst, src) edge so that
//        the copy-related pair remains a candidate for coalescing.
//   3. Call clobber: for every Call/CallImport i, add an edge between every
//        v ∈ live_after[i] and every caller-saved physical register node.

use std::collections::{HashMap, HashSet};

use crate::assembler::liveness::LivenessInfo;
use crate::cfg::three_address_code::{FunctionIR, InstrKind, Type, ValueId};

// ---------------------------------------------------------------------------
// Physical register model
// ---------------------------------------------------------------------------

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PhysReg {
    // Caller-saved (clobbered across calls)
    Rax,
    Rcx,
    Rdx,
    Rsi,
    Rdi,
    R8,
    R9,
    R10,
    R11,
    // Callee-saved (must be preserved)
    Rbx,
    R12,
    R13,
    R14,
    R15,
}

/// All allocatable registers (RSP and RBP are excluded).
pub const ALL_REGS: [PhysReg; 14] = [
    PhysReg::Rax,
    PhysReg::Rcx,
    PhysReg::Rdx,
    PhysReg::Rsi,
    PhysReg::Rdi,
    PhysReg::R8,
    PhysReg::R9,
    PhysReg::R10,
    PhysReg::R11,
    PhysReg::Rbx,
    PhysReg::R12,
    PhysReg::R13,
    PhysReg::R14,
    PhysReg::R15,
];

pub const CALLER_SAVED: [PhysReg; 9] = [
    PhysReg::Rax,
    PhysReg::Rcx,
    PhysReg::Rdx,
    PhysReg::Rsi,
    PhysReg::Rdi,
    PhysReg::R8,
    PhysReg::R9,
    PhysReg::R10,
    PhysReg::R11,
];

pub const CALLEE_SAVED: [PhysReg; 5] = [
    PhysReg::Rbx,
    PhysReg::R12,
    PhysReg::R13,
    PhysReg::R14,
    PhysReg::R15,
];

/// Total number of allocatable registers = K for graph coloring.
pub const K: usize = ALL_REGS.len(); // 14

impl PhysReg {
    /// x86-64 register name for a 32-bit (i32/i1) value.
    pub fn name32(self) -> &'static str {
        match self {
            PhysReg::Rax => "%eax",
            PhysReg::Rcx => "%ecx",
            PhysReg::Rdx => "%edx",
            PhysReg::Rsi => "%esi",
            PhysReg::Rdi => "%edi",
            PhysReg::R8 => "%r8d",
            PhysReg::R9 => "%r9d",
            PhysReg::R10 => "%r10d",
            PhysReg::R11 => "%r11d",
            PhysReg::Rbx => "%ebx",
            PhysReg::R12 => "%r12d",
            PhysReg::R13 => "%r13d",
            PhysReg::R14 => "%r14d",
            PhysReg::R15 => "%r15d",
        }
    }

    /// x86-64 register name for a 64-bit (i64/ptr) value.
    pub fn name64(self) -> &'static str {
        match self {
            PhysReg::Rax => "%rax",
            PhysReg::Rcx => "%rcx",
            PhysReg::Rdx => "%rdx",
            PhysReg::Rsi => "%rsi",
            PhysReg::Rdi => "%rdi",
            PhysReg::R8 => "%r8",
            PhysReg::R9 => "%r9",
            PhysReg::R10 => "%r10",
            PhysReg::R11 => "%r11",
            PhysReg::Rbx => "%rbx",
            PhysReg::R12 => "%r12",
            PhysReg::R13 => "%r13",
            PhysReg::R14 => "%r14",
            PhysReg::R15 => "%r15",
        }
    }

    /// Returns the appropriate register name based on `ty`.
    pub fn name_for_type(self, ty: &Type) -> &'static str {
        match ty {
            Type::I64 | Type::Ptr(_) => self.name64(),
            _ => self.name32(), // I1, I32
        }
    }

    /// ABI argument register for the i-th argument (0-indexed), 32-bit.
    /// Returns None if the argument index exceeds the register count (6).
    pub fn arg32(i: usize) -> Option<PhysReg> {
        [
            PhysReg::Rdi,
            PhysReg::Rsi,
            PhysReg::Rdx,
            PhysReg::Rcx,
            PhysReg::R8,
            PhysReg::R9,
        ]
        .get(i)
        .copied()
    }

    /// ABI argument register for the i-th argument (0-indexed), 64-bit.
    pub fn arg64(i: usize) -> Option<PhysReg> {
        Self::arg32(i) // same physical register
    }
}

// ---------------------------------------------------------------------------
// Node type
// ---------------------------------------------------------------------------

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum NodeId {
    Virtual(ValueId),
    Physical(PhysReg),
}

// ---------------------------------------------------------------------------
// Graph
// ---------------------------------------------------------------------------

pub struct InterferenceGraph {
    /// Undirected adjacency list.  Every edge (u,v) is stored in both
    /// `adj[u]` and `adj[v]`.
    pub adj: HashMap<NodeId, HashSet<NodeId>>,

    /// Copy-related pairs produced by `Assign` instructions.  These pairs
    /// are candidates for Briggs coalescing.  Stored with the smaller-id
    /// node first (by debug ordering) for deduplication.
    pub copy_related: HashSet<(NodeId, NodeId)>,
}

impl InterferenceGraph {
    pub fn new() -> Self {
        InterferenceGraph {
            adj: HashMap::new(),
            copy_related: HashSet::new(),
        }
    }

    /// Add an undirected edge between `u` and `v`.  Self-edges are ignored.
    pub fn add_edge(&mut self, u: NodeId, v: NodeId) {
        if u == v {
            return;
        }
        self.adj.entry(u).or_default().insert(v);
        self.adj.entry(v).or_default().insert(u);
    }

    /// Ensure a node exists in the graph even if it has no edges yet.
    pub fn ensure_node(&mut self, n: NodeId) {
        self.adj.entry(n).or_default();
    }

    /// Number of neighbours of `n`.
    pub fn degree(&self, n: NodeId) -> usize {
        self.adj.get(&n).map(|s| s.len()).unwrap_or(0)
    }

    /// Iterator over every neighbour of `n`.
    pub fn neighbors(&self, n: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.adj.get(&n).into_iter().flat_map(|s| s.iter().copied())
    }
}

// ---------------------------------------------------------------------------
// Graph construction
// ---------------------------------------------------------------------------

/// True iff `v` should participate in register allocation.
fn is_allocatable(v: ValueId, func: &FunctionIR) -> bool {
    func.values
        .get(&v)
        .map(|i| i.ty != Type::Mem && i.ty != Type::Void && i.ty != Type::None)
        .unwrap_or(false)
}

/// Build the interference graph for `func` given pre-computed liveness info.
pub fn build_interference_graph(func: &FunctionIR, liveness: &LivenessInfo) -> InterferenceGraph {
    let mut g = InterferenceGraph::new();

    // Seed every allocatable virtual value as a node (even if it ends up with
    // no edges, e.g. a value used only once right after its definition).
    for (&vid, info) in &func.values {
        if info.ty != Type::Mem && info.ty != Type::Void && info.ty != Type::None {
            g.ensure_node(NodeId::Virtual(vid));
        }
    }
    // Seed all physical registers as nodes.
    for &pr in &ALL_REGS {
        g.ensure_node(NodeId::Physical(pr));
    }

    for block in &func.blocks {
        for instr in &block.instrs {
            // Collect allocatable defs produced by this instruction.
            let defs: Vec<ValueId> = instr
                .results
                .iter()
                .copied()
                .filter(|&v| is_allocatable(v, func))
                .collect();

            let live_set = match liveness.live_after.get(&instr.id) {
                Some(s) => s,
                None => continue,
            };

            let copy_src: Option<ValueId> = match &instr.kind {
                InstrKind::Assign { src, .. } => Some(*src),
                _ => None,
            };

            // Rule 1 (+ Rule 2 copy exception):
            // For every def d and every value v live after the instruction,
            // d and v must be in different registers — unless they are the
            // copy-related pair from an Assign.
            for &def in &defs {
                let def_node = NodeId::Virtual(def);
                for &live_val in live_set {
                    if live_val == def {
                        continue; // a value never interferes with itself
                    }
                    let live_node = NodeId::Virtual(live_val);
                    if copy_src == Some(live_val) {
                        // Copy exception: record as coalescing candidate,
                        // do NOT add an interference edge.
                        g.copy_related.insert((def_node, live_node));
                    } else {
                        g.add_edge(def_node, live_node);
                    }
                }
            }

            // Rule 3 (call clobber):
            // Every value live across a Call or CallImport must not be placed
            // in a caller-saved register, so add interference edges between
            // each live value and every caller-saved physical register.
            if matches!(
                &instr.kind,
                InstrKind::Call { .. } | InstrKind::CallImport { .. }
            ) {
                for &live_val in live_set {
                    let vn = NodeId::Virtual(live_val);
                    for &cr in &CALLER_SAVED {
                        g.add_edge(vn, NodeId::Physical(cr));
                    }
                }
            }
        }
    }

    g
}
