use std::collections::HashMap;

use super::super::cfg::three_address_code::{
    BlockId, FunctionIR, Instr, InstrId, InstrKind, ProgramIR, Type, ValueId, ValueInfo,
};

// Replace all phi nodes with Assign instructions inserted into predecessor blocks.
//
// For each phi node in block T with result `r` and incoming (pred, src) pairs:
//   - In each predecessor block P, append Assign instructions that copy the
//     incoming value `src` into `r`.
//   - Remove the phi node from T.
//
// To handle the parallel-copy problem (where one phi's result appears as the
// incoming value for another phi from the same predecessor), we use a two-phase
// approach mirroring the push/pop strategy in codegen_no_reg.rs:
//   Phase 1 – read each incoming value into a fresh temporary.
//   Phase 2 – write each temporary to its phi result destination.
//
// This guarantees all reads happen before any writes, even in "swap" scenarios
// such as:  %a = phi [P: %b],  %b = phi [P: %a]

pub fn remove_phis(program: &mut ProgramIR) {
    for func in program.functions.values_mut() {
        remove_phis_in_function(func);
    }
}

fn remove_phis_in_function(func: &mut FunctionIR) {
    // Determine the next fresh InstrId and ValueId to use.
    let mut next_instr_id: u32 = func
        .blocks
        .iter()
        .flat_map(|b| {
            b.instrs
                .iter()
                .map(|i| i.id.0)
                .chain(b.phis.iter().map(|p| p.id.0))
                .chain(b.mem_in.iter().map(|p| p.id.0))
        })
        .max()
        .map(|m| m + 1)
        .unwrap_or(0);

    let mut next_value_id: u32 = func
        .values
        .keys()
        .map(|v| v.0)
        .max()
        .map(|m| m + 1)
        .unwrap_or(0);

    // Instructions to append to each predecessor block (keyed by block index).
    let mut inserts: HashMap<usize, Vec<Instr>> = HashMap::new();
    // New ValueInfos for the fresh temporaries.
    let mut new_values: Vec<(ValueId, ValueInfo)> = Vec::new();

    for t_idx in 0..func.blocks.len() {
        // Collect value-carrying phis (skip Mem/Void/None tokens).
        let phis: Vec<_> = func.blocks[t_idx]
            .phis
            .iter()
            .filter(|phi| !matches!(phi.ty, Type::Mem | Type::Void | Type::None))
            .cloned()
            .collect();

        if phis.is_empty() {
            continue;
        }

        // Group copies by predecessor:
        //   pred_id -> [(src = incoming_val, dst = phi.result, ty = phi.ty)]
        let mut pred_copies: HashMap<BlockId, Vec<(ValueId, ValueId, Type)>> = HashMap::new();
        for phi in &phis {
            for &(pred_id, src_val) in &phi.incomings {
                pred_copies
                    .entry(pred_id)
                    .or_default()
                    .push((src_val, phi.result, phi.ty.clone()));
            }
        }

        for (pred_id, copies) in pred_copies {
            let pred_idx = func.block_id_to_ind[&pred_id];
            let block_instrs = inserts.entry(pred_idx).or_default();

            // Phase 1: copy each incoming value into a fresh temporary.
            let mut temps: Vec<ValueId> = Vec::new();
            for (src_val, _dst, ty) in &copies {
                let temp = ValueId(next_value_id);
                next_value_id += 1;
                let instr_id = InstrId(next_instr_id);
                next_instr_id += 1;

                temps.push(temp);
                block_instrs.push(Instr {
                    id: instr_id,
                    results: vec![temp],
                    kind: InstrKind::Assign {
                        ty: ty.clone(),
                        src: *src_val,
                    },
                });
                new_values.push((
                    temp,
                    ValueInfo {
                        ty: ty.clone(),
                        declared_by: Some(instr_id),
                        use_chain: vec![],
                        org_name: String::new(),
                        debug_name: format!("phi_tmp_{}", temp.0),
                    },
                ));
            }

            // Phase 2: write temporaries into the phi result destinations.
            for (i, (_src_val, dst, ty)) in copies.iter().enumerate() {
                let instr_id = InstrId(next_instr_id);
                next_instr_id += 1;
                block_instrs.push(Instr {
                    id: instr_id,
                    results: vec![*dst],
                    kind: InstrKind::Assign {
                        ty: ty.clone(),
                        src: temps[i],
                    },
                });
            }
        }
    }

    // Append the generated Assign instructions to their predecessor blocks.
    for (pred_idx, new_instrs) in inserts {
        func.blocks[pred_idx].instrs.extend(new_instrs);
    }

    // Remove all phi nodes (both value phis and mem_in) from every block.
    for block in &mut func.blocks {
        block.phis.clear();
        block.mem_in = None;
    }

    // Register new temporaries so subsequent passes (e.g. register allocator)
    // can allocate storage for them.
    for (vid, info) in new_values {
        func.values.insert(vid, info);
    }
}
