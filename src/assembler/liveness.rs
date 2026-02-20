// Liveness analysis for register allocation.
//
// Computes three sets:
//   live_in[B]     – values live at the start of block B
//   live_out[B]    – values live at the end of block B
//   live_after[i]  – values live immediately after instruction i
//
// Only non-Mem-typed values are tracked; Mem tokens are sequencing artefacts
// and are never assigned to registers.

use std::collections::{HashMap, HashSet};

use crate::cfg::three_address_code::{
    BlockId, FunctionIR, InstrId, InstrKind, Terminator, Type, ValueId,
};

// ---------------------------------------------------------------------------
// Public output type
// ---------------------------------------------------------------------------

pub struct LivenessInfo {
    pub live_in: HashMap<BlockId, HashSet<ValueId>>,
    pub live_out: HashMap<BlockId, HashSet<ValueId>>,
    /// For each non-phi instruction, the set of values live *after* it runs.
    pub live_after: HashMap<InstrId, HashSet<ValueId>>,
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// True iff `v` should participate in register allocation.
#[inline]
fn is_allocatable(v: ValueId, func: &FunctionIR) -> bool {
    func.values
        .get(&v)
        .map(|info| info.ty != Type::Mem && info.ty != Type::Void && info.ty != Type::None)
        .unwrap_or(false)
}

/// All ValueIds that `kind` reads, regardless of type.
/// Filtering by `is_allocatable` is done at each call site.
fn raw_instr_uses(kind: &InstrKind) -> Vec<ValueId> {
    match kind {
        InstrKind::Const(_)
        | InstrKind::GlobalAddr { .. }
        | InstrKind::GlobalArrayAddr { .. }
        | InstrKind::GlobalStrAddr { .. }
        | InstrKind::Len { .. }
        | InstrKind::Alloca { .. } => vec![],

        InstrKind::BinOp { lhs, rhs, .. } => vec![*lhs, *rhs],
        InstrKind::UnOp { arg, .. } => vec![*arg],
        InstrKind::ICmp { lhs, rhs, .. } => vec![*lhs, *rhs],
        InstrKind::Cast { src, .. } => vec![*src],
        InstrKind::ElemAddr { base, index, .. } => vec![*base, *index],
        InstrKind::Load { mem, addr, .. } => vec![*mem, *addr],
        InstrKind::Store { mem, addr, value, .. } => vec![*mem, *addr, *value],
        InstrKind::Call { mem, args, .. } | InstrKind::CallImport { mem, args, .. } => {
            let mut v = vec![*mem];
            v.extend_from_slice(args);
            v
        }
        InstrKind::Assign { src, .. } => vec![*src],
    }
}

/// Non-Mem uses of `kind`.
fn instr_uses(kind: &InstrKind, func: &FunctionIR) -> Vec<ValueId> {
    raw_instr_uses(kind)
        .into_iter()
        .filter(|&v| is_allocatable(v, func))
        .collect()
}

/// Non-Mem defs produced by an instruction.
fn instr_defs(results: &[ValueId], func: &FunctionIR) -> Vec<ValueId> {
    results
        .iter()
        .copied()
        .filter(|&v| is_allocatable(v, func))
        .collect()
}

/// Non-Mem uses of a terminator (Mem sequencing tokens excluded).
fn term_uses(term: &Terminator, func: &FunctionIR) -> Vec<ValueId> {
    let raw: Vec<ValueId> = match term {
        Terminator::Br { .. } | Terminator::RetVoid { .. } | Terminator::Unreachable => vec![],
        Terminator::CBr { cond, .. } => vec![*cond],
        Terminator::Ret { value, .. } => vec![*value],
    };
    raw.into_iter()
        .filter(|&v| is_allocatable(v, func))
        .collect()
}

/// Block IDs reachable in one step from `term`.
fn successors(term: &Terminator) -> Vec<BlockId> {
    match term {
        Terminator::Br { target, .. } => vec![*target],
        Terminator::CBr { then_bb, else_bb, .. } => vec![*then_bb, *else_bb],
        Terminator::Ret { .. } | Terminator::RetVoid { .. } | Terminator::Unreachable => vec![],
    }
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

pub fn compute_liveness(func: &FunctionIR) -> LivenessInfo {
    // -----------------------------------------------------------------------
    // Phase 1: per-block UEVar (upward-exposed) and VarKill sets.
    //
    // ue_var[B]  = values used in B before any local definition.
    // var_kill[B]= values defined (killed) somewhere in B.
    // -----------------------------------------------------------------------
    let mut ue_var: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();
    let mut var_kill: HashMap<BlockId, HashSet<ValueId>> = HashMap::new();

    for block in &func.blocks {
        let mut local_ue: HashSet<ValueId> = HashSet::new();
        let mut local_kill: HashSet<ValueId> = HashSet::new();

        for instr in &block.instrs {
            // Uses: upward-exposed if not yet killed locally.
            for used in instr_uses(&instr.kind, func) {
                if !local_kill.contains(&used) {
                    local_ue.insert(used);
                }
            }
            // Defs.
            for def in instr_defs(&instr.results, func) {
                local_kill.insert(def);
            }
        }

        // Terminator uses.
        for used in term_uses(&block.term, func) {
            if !local_kill.contains(&used) {
                local_ue.insert(used);
            }
        }

        ue_var.insert(block.id, local_ue);
        var_kill.insert(block.id, local_kill);
    }

    // -----------------------------------------------------------------------
    // Phase 2: backward dataflow iteration until fixed point.
    //
    //   live_out[B] = ∪ live_in[S]  for each successor S
    //   live_in[B]  = ue_var[B] ∪ (live_out[B] − var_kill[B])
    // -----------------------------------------------------------------------
    let mut live_in: HashMap<BlockId, HashSet<ValueId>> =
        func.blocks.iter().map(|b| (b.id, HashSet::new())).collect();
    let mut live_out: HashMap<BlockId, HashSet<ValueId>> =
        func.blocks.iter().map(|b| (b.id, HashSet::new())).collect();

    // Collect block ids in reverse order (approximates reverse-postorder for
    // faster convergence without needing a full DFS).
    let block_ids: Vec<BlockId> = func.blocks.iter().rev().map(|b| b.id).collect();

    let mut changed = true;
    while changed {
        changed = false;
        for &bid in &block_ids {
            let bidx = func.block_id_to_ind[&bid];
            let term = &func.blocks[bidx].term;

            // live_out[B] = ∪ live_in[S]
            let mut new_out: HashSet<ValueId> = HashSet::new();
            for succ in successors(term) {
                if let Some(s_in) = live_in.get(&succ) {
                    new_out.extend(s_in.iter().copied());
                }
            }

            // live_in[B] = ue_var[B] ∪ (live_out[B] - var_kill[B])
            let empty = HashSet::new();
            let ue = ue_var.get(&bid).unwrap_or(&empty);
            let kill = var_kill.get(&bid).unwrap_or(&empty);
            let mut new_in: HashSet<ValueId> = ue.clone();
            for &v in &new_out {
                if !kill.contains(&v) {
                    new_in.insert(v);
                }
            }

            if new_out != live_out[&bid] || new_in != live_in[&bid] {
                live_out.insert(bid, new_out);
                live_in.insert(bid, new_in);
                changed = true;
            }
        }
    }

    // -----------------------------------------------------------------------
    // Phase 3: per-instruction live sets via backward sweep.
    //
    // For each block, seed with live_out[B] then sweep instructions in
    // reverse, recording live_after[i] before removing defs and adding uses.
    // -----------------------------------------------------------------------
    let mut live_after: HashMap<InstrId, HashSet<ValueId>> = HashMap::new();

    for block in &func.blocks {
        let mut live: HashSet<ValueId> = live_out[&block.id].clone();

        // Terminator uses are live at the end of the block (before the
        // terminator fires), so they must survive through all instructions.
        for used in term_uses(&block.term, func) {
            live.insert(used);
        }

        // Sweep in reverse instruction order.
        for instr in block.instrs.iter().rev() {
            // Record what is live after this instruction completes.
            live_after.insert(instr.id, live.clone());

            // Remove defs (they are "born" here).
            for def in instr_defs(&instr.results, func) {
                live.remove(&def);
            }

            // Add uses (they must be live before this instruction).
            for used in instr_uses(&instr.kind, func) {
                live.insert(used);
            }
        }
    }

    LivenessInfo {
        live_in,
        live_out,
        live_after,
    }
}
