// Chaitin-Briggs graph-coloring register allocator.
//
// Phases:
//   1. Briggs coalescing  – try to merge copy-related pairs that satisfy the
//      Briggs criterion, eliminating the corresponding Assign instructions.
//   2. Simplify + spill selection – repeatedly remove low-degree virtual nodes
//      onto a select stack; when all remaining nodes are high-degree, pick the
//      cheapest potential spill and push it.
//   3. Select – pop the stack in LIFO order, assigning the lowest-cost
//      available color to each node; nodes that cannot be colored become
//      actual spills and receive a dedicated stack slot.
//
// The output is a RegAlloc mapping every allocatable ValueId to either a
// PhysReg or a %rbp-relative stack offset.

use std::collections::{HashMap, HashSet};

use crate::assembler::interference_graph::{
    build_interference_graph, InterferenceGraph, NodeId, PhysReg, ALL_REGS, CALLEE_SAVED,
    CALLER_SAVED, K,
};
use crate::assembler::liveness::compute_liveness;
use crate::cfg::three_address_code::{FunctionIR, ProgramIR, Type, ValueId};

// ---------------------------------------------------------------------------
// Public output types
// ---------------------------------------------------------------------------

/// Where a virtual value lives after register allocation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Location {
    /// Assigned to a physical register.
    Reg(PhysReg),
    /// Spilled to the stack; offset from %rbp (always negative, e.g. -8).
    Spill(i32),
}

/// Complete register-allocation result for one function.
#[derive(Debug)]
pub struct RegAlloc {
    /// Maps every allocatable ValueId to its assigned location.
    pub loc: HashMap<ValueId, Location>,
    /// Callee-saved registers actually assigned; prologue must push/pop these.
    pub callee_saves_used: Vec<PhysReg>,
    /// Total spill-area size in bytes (positive, 16-byte aligned).
    /// Does not include the space consumed by pushed callee-saved registers.
    pub frame_size: i32,
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

/// Run Chaitin-Briggs register allocation for every function in `program_ir`.
///
/// Returns a map from function name to its `RegAlloc` result.  Functions are
/// processed in sorted name order so the output is deterministic.
pub fn allocate_program(program_ir: &ProgramIR) -> HashMap<String, RegAlloc> {
    let mut func_names: Vec<&String> = program_ir.functions.keys().collect();
    func_names.sort();

    func_names
        .into_iter()
        .map(|name| {
            let func = &program_ir.functions[name];
            let liveness = compute_liveness(func);
            let ig = build_interference_graph(func, &liveness);
            let ra = allocate_registers(func, &ig);
            (name.clone(), ra)
        })
        .collect()
}

/// Run Chaitin-Briggs register allocation on `func` given a pre-built
/// `InterferenceGraph`.  The graph is not mutated; a working copy is made.
pub fn allocate_registers(func: &FunctionIR, ig: &InterferenceGraph) -> RegAlloc {
    // -----------------------------------------------------------------------
    // Working copies – coalescing and simplify both mutate these.
    // -----------------------------------------------------------------------
    let mut adj: HashMap<NodeId, HashSet<NodeId>> = ig.adj.clone();
    let mut degree: HashMap<NodeId, usize> =
        adj.iter().map(|(&n, s)| (n, s.len())).collect();

    // -----------------------------------------------------------------------
    // Phase 1 – Briggs coalescing
    // -----------------------------------------------------------------------
    let alias = do_coalesce(&mut adj, &mut degree, &ig.copy_related);

    // Virtual nodes still present in the working graph after coalescing.
    // (Merged-away nodes were removed from `adj` inside `merge_into`.)
    let mut virtual_nodes: Vec<NodeId> = adj
        .keys()
        .copied()
        .filter(|n| matches!(n, NodeId::Virtual(_)))
        .collect();
    // Sort for deterministic output.
    virtual_nodes.sort_by_key(|n| match n {
        NodeId::Virtual(v) => v.0,
        NodeId::Physical(_) => 0,
    });

    // -----------------------------------------------------------------------
    // Phase 2 – Simplify + spill selection
    // -----------------------------------------------------------------------
    let (select_stack, potential_spills) =
        do_simplify(&adj, degree, &virtual_nodes, func);

    // -----------------------------------------------------------------------
    // Phase 3 – Select (pop stack, assign colors)
    // -----------------------------------------------------------------------
    let (mut coloring, actual_spill_nodes) =
        do_select(&select_stack, &adj, &potential_spills, &ig.copy_related);

    // Propagate colors through alias chains so every coalesced-away node
    // gets the same register as its canonical representative.
    propagate_alias_colors(&alias, &mut coloring);

    // -----------------------------------------------------------------------
    // Build the output RegAlloc
    // -----------------------------------------------------------------------
    let mut loc: HashMap<ValueId, Location> = HashMap::new();
    let mut callee_saves_used: HashSet<PhysReg> = HashSet::new();
    let mut spill_offset: i32 = 0; // grows downward from %rbp

    // Assign stack slots to values that could not be colored.
    for node in &actual_spill_nodes {
        if let NodeId::Virtual(v) = node {
            if let Some(info) = func.values.get(v) {
                let sz = type_size_bytes(&info.ty);
                spill_offset -= sz;
                loc.insert(*v, Location::Spill(spill_offset));
            }
        }
    }

    // Assign registers to all successfully colored virtual nodes.
    for (&node, &reg) in &coloring {
        if let NodeId::Virtual(v) = node {
            if !loc.contains_key(&v) {
                loc.insert(v, Location::Reg(reg));
                if CALLEE_SAVED.contains(&reg) {
                    callee_saves_used.insert(reg);
                }
            }
        }
    }

    let frame_size = align16(-spill_offset);
    let mut callee_saves: Vec<PhysReg> = callee_saves_used.into_iter().collect();
    callee_saves.sort();

    RegAlloc {
        loc,
        callee_saves_used: callee_saves,
        frame_size,
    }
}

// ---------------------------------------------------------------------------
// Phase 1: Briggs coalescing
// ---------------------------------------------------------------------------

/// Try to merge copy-related pairs using the Briggs criterion.
///
/// The loop repeats until no more coalescings are possible, because merging
/// one pair can expose new safe coalescings (degrees change after a merge).
///
/// Returns an alias map `{ removed_node → canonical_representative }`.
fn do_coalesce(
    adj: &mut HashMap<NodeId, HashSet<NodeId>>,
    degree: &mut HashMap<NodeId, usize>,
    copy_related: &HashSet<(NodeId, NodeId)>,
) -> HashMap<NodeId, NodeId> {
    let mut alias: HashMap<NodeId, NodeId> = HashMap::new();

    loop {
        let mut coalesced_any = false;

        // Resolve canonical representatives before each sweep so we don't
        // try to coalesce a node that has already been merged away.
        let pairs: Vec<(NodeId, NodeId)> = copy_related
            .iter()
            .map(|&(a, b)| (get_alias(&alias, a), get_alias(&alias, b)))
            .filter(|(a, b)| a != b)
            .collect();

        for (a, b) in pairs {
            // One or both nodes may have been merged in this same sweep.
            if !adj.contains_key(&a) || !adj.contains_key(&b) {
                continue;
            }
            // Cannot coalesce nodes that already interfere.
            if adj.get(&a).map_or(false, |s| s.contains(&b)) {
                continue;
            }
            // Briggs criterion: safe to coalesce?
            if !briggs_ok(adj, degree, a, b) {
                continue;
            }

            merge_into(adj, a, b);
            // Recompute degrees from scratch after the structural change.
            *degree = adj.iter().map(|(&n, s)| (n, s.len())).collect();
            alias.insert(b, a);
            coalesced_any = true;
        }

        if !coalesced_any {
            break;
        }
    }

    alias
}

/// Briggs criterion: it is safe to coalesce `a` and `b` if the number of
/// high-degree (≥ K) nodes in their *combined* neighbor set is less than K.
///
/// This guarantees the merged node can still be colored: it has at most K-1
/// high-degree neighbors forcing K-1 distinct colors, leaving ≥ 1 free.
fn briggs_ok(
    adj: &HashMap<NodeId, HashSet<NodeId>>,
    degree: &HashMap<NodeId, usize>,
    a: NodeId,
    b: NodeId,
) -> bool {
    let empty = HashSet::new();
    let a_nbrs = adj.get(&a).unwrap_or(&empty);
    let b_nbrs = adj.get(&b).unwrap_or(&empty);

    let high_count = a_nbrs
        .union(b_nbrs)
        .filter(|&&n| n != a && n != b)
        .filter(|&&n| degree.get(&n).copied().unwrap_or(0) >= K)
        .count();

    high_count < K
}

/// Merge node `b` into node `a`: redirect all of `b`'s edges to `a` and
/// remove `b` from the adjacency structure entirely.
fn merge_into(adj: &mut HashMap<NodeId, HashSet<NodeId>>, a: NodeId, b: NodeId) {
    let b_neighbors: Vec<NodeId> = adj.remove(&b).unwrap_or_default().into_iter().collect();

    for nbr in b_neighbors {
        if nbr == a {
            continue; // (a,b) edge disappears when b is absorbed
        }
        // Remove b from nbr's adjacency list.
        if let Some(s) = adj.get_mut(&nbr) {
            s.remove(&b);
        }
        // Add edge (a, nbr) if not already present.
        adj.entry(a).or_default().insert(nbr);
        adj.entry(nbr).or_default().insert(a);
    }
}

/// Chase the alias chain to find the canonical representative of `n`.
fn get_alias(alias: &HashMap<NodeId, NodeId>, mut n: NodeId) -> NodeId {
    while let Some(&next) = alias.get(&n) {
        n = next;
    }
    n
}

/// Propagate colors through alias chains so that every coalesced-away node
/// ends up with the same register as its canonical representative.
fn propagate_alias_colors(
    alias: &HashMap<NodeId, NodeId>,
    coloring: &mut HashMap<NodeId, PhysReg>,
) {
    // Iterate until stable to handle multi-hop chains (a→b→c).
    let mut changed = true;
    while changed {
        changed = false;
        for (&coalesced, _) in alias {
            if coloring.contains_key(&coalesced) {
                continue;
            }
            let canon = get_alias(alias, coalesced);
            if let Some(&color) = coloring.get(&canon) {
                coloring.insert(coalesced, color);
                changed = true;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Phase 2: Simplify + spill selection
// ---------------------------------------------------------------------------

/// Push all virtual nodes onto a select stack.
///
/// Each iteration of the outer loop either:
///  - simplifies: pushes a low-degree node (working_degree < K) — guaranteed
///    colorable later, never an actual spill.
///  - or spills: pushes the minimum-cost candidate when no low-degree node
///    exists — may or may not be colorable during Select.
///
/// Returns `(select_stack, set_of_potential_spills)`.
fn do_simplify(
    adj: &HashMap<NodeId, HashSet<NodeId>>,
    initial_degree: HashMap<NodeId, usize>,
    virtual_nodes: &[NodeId],
    func: &FunctionIR,
) -> (Vec<NodeId>, HashSet<NodeId>) {
    // working_degree[v] = number of active neighbors of v still in in_graph,
    // plus all physical register neighbors (which never leave).
    let mut working_degree = initial_degree;
    let mut in_graph: HashSet<NodeId> = virtual_nodes.iter().copied().collect();
    let mut stack: Vec<NodeId> = Vec::new();
    let mut potential_spills: HashSet<NodeId> = HashSet::new();

    while !in_graph.is_empty() {
        // Collect low-degree candidates (sorted for determinism).
        let mut low: Vec<NodeId> = in_graph
            .iter()
            .copied()
            .filter(|n| working_degree.get(n).copied().unwrap_or(0) < K)
            .collect();
        low.sort_by_key(|n| match n {
            NodeId::Virtual(v) => v.0,
            NodeId::Physical(_) => 0,
        });

        let (node, is_spill) = if let Some(&v) = low.first() {
            // Simplify: this node is guaranteed colorable.
            (v, false)
        } else {
            // All remaining nodes have working_degree ≥ K.
            // Pick the one with minimum spill priority (cheapest to spill,
            // highest benefit from removal).
            let v = in_graph
                .iter()
                .copied()
                .min_by(|&a, &b| {
                    spill_priority(a, func, &working_degree)
                        .partial_cmp(&spill_priority(b, func, &working_degree))
                        .unwrap_or(std::cmp::Ordering::Equal)
                })
                .expect("in_graph is non-empty");
            (v, true)
        };

        in_graph.remove(&node);
        stack.push(node);
        if is_spill {
            potential_spills.insert(node);
        }

        // Decrement working_degree for virtual neighbors still in the graph.
        // Physical register nodes are never in in_graph; their contribution
        // to working_degree is permanent and does not change.
        if let Some(neighbors) = adj.get(&node) {
            for &nbr in neighbors {
                if in_graph.contains(&nbr) {
                    if let Some(d) = working_degree.get_mut(&nbr) {
                        *d = d.saturating_sub(1);
                    }
                }
            }
        }
    }

    (stack, potential_spills)
}

/// Spill priority: **lower = better candidate to spill**.
///
///   priority = (defs + uses) / degree
///
/// A node with few defs/uses is cheap to spill (fewer load/store insertions).
/// A high-degree node yields greater benefit when removed (unblocks more
/// neighbours).  Minimising the ratio picks the cheapest-per-benefit spill.
fn spill_priority(node: NodeId, func: &FunctionIR, degree: &HashMap<NodeId, usize>) -> f64 {
    let v = match node {
        NodeId::Virtual(v) => v,
        NodeId::Physical(_) => return f64::INFINITY, // never spill physical regs
    };
    let info = match func.values.get(&v) {
        Some(i) => i,
        None => return f64::INFINITY,
    };
    let uses = info.use_chain.len() as f64;
    let defs = if info.declared_by.is_some() { 1.0 } else { 0.0 };
    let cost = uses + defs;
    let benefit = degree.get(&node).copied().unwrap_or(1) as f64;
    cost / benefit.max(1.0)
}

// ---------------------------------------------------------------------------
// Phase 3: Select
// ---------------------------------------------------------------------------

/// Pop the select stack in LIFO order and assign a color to each node.
///
/// Key invariant: a node pushed during Simplify (non-potential-spill) had
/// working_degree < K at push time.  Those neighbors are the ones popped
/// *before* the node itself (pushed after it in stack order), so they are
/// already colored when the node is processed.  The forbidden set therefore
/// has at most K-1 entries, guaranteeing a free color exists.
///
/// A node pushed during Spill selection has no such guarantee and may fail.
///
/// Returns `(coloring: NodeId → PhysReg, actual_spills: Vec<NodeId>)`.
fn do_select(
    select_stack: &[NodeId],
    adj: &HashMap<NodeId, HashSet<NodeId>>,
    potential_spills: &HashSet<NodeId>,
    copy_related: &HashSet<(NodeId, NodeId)>,
) -> (HashMap<NodeId, PhysReg>, Vec<NodeId>) {
    // Pre-color all physical registers: they are never on the select stack
    // but appear as neighbors and must be in the coloring map.
    let mut coloring: HashMap<NodeId, PhysReg> = ALL_REGS
        .iter()
        .map(|&pr| (NodeId::Physical(pr), pr))
        .collect();

    let mut actual_spills: Vec<NodeId> = Vec::new();

    // Process in LIFO order: last-pushed (potential spills, high-degree at
    // push time) are colored first; first-pushed (low-degree, guaranteed
    // colorable) are colored last.
    for &node in select_stack.iter().rev() {
        // Forbidden colors = colors already assigned to neighbors.
        let forbidden: HashSet<PhysReg> = adj
            .get(&node)
            .into_iter()
            .flat_map(|s| s.iter())
            .filter_map(|n| coloring.get(n).copied())
            .collect();

        let available: Vec<PhysReg> = ALL_REGS
            .iter()
            .copied()
            .filter(|r| !forbidden.contains(r))
            .collect();

        if available.is_empty() {
            // This can only happen for nodes that were pushed as potential
            // spills (high-degree at push time, too many constraints).
            debug_assert!(
                potential_spills.contains(&node),
                "low-degree node ran out of colors (algorithm invariant violated)"
            );
            actual_spills.push(node);
        } else {
            // Optional hint: if a copy-related partner already has a usable
            // color, prefer it (eliminates the Assign instruction for free).
            let hint = copy_hint(node, copy_related, &coloring, &available);
            coloring.insert(node, pick_color(&available, hint));
        }
    }

    (coloring, actual_spills)
}

/// Return the color of any already-colored copy-related partner of `node`
/// that is also in `available`, or `None` if no such color exists.
fn copy_hint(
    node: NodeId,
    copy_related: &HashSet<(NodeId, NodeId)>,
    coloring: &HashMap<NodeId, PhysReg>,
    available: &[PhysReg],
) -> Option<PhysReg> {
    copy_related
        .iter()
        .filter_map(|(a, b)| {
            let partner = if *a == node {
                *b
            } else if *b == node {
                *a
            } else {
                return None;
            };
            let color = coloring.get(&partner).copied()?;
            available.contains(&color).then_some(color)
        })
        .next()
}

/// Select a register from `available`.
///
/// Priority order:
///  1. The copy-related hint (eliminates an Assign instruction).
///  2. A caller-saved register (no prologue save/restore overhead).
///  3. Any remaining available register.
fn pick_color(available: &[PhysReg], hint: Option<PhysReg>) -> PhysReg {
    if let Some(h) = hint {
        if available.contains(&h) {
            return h;
        }
    }
    available
        .iter()
        .copied()
        .find(|r| CALLER_SAVED.contains(r))
        .unwrap_or(available[0])
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn type_size_bytes(ty: &Type) -> i32 {
    match ty {
        Type::I1 | Type::I32 => 4,
        Type::I64 | Type::Ptr(_) => 8,
        Type::I8 => 1,
        _ => 8, // conservative
    }
}

/// Round `n` up to the nearest multiple of 16 (x86-64 ABI stack alignment).
fn align16(n: i32) -> i32 {
    if n == 0 {
        0
    } else {
        (n + 15) & !15
    }
}
