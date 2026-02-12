use super::three_address_code::*;
use std::collections::HashMap;
use std::fmt::Write;

/// Print an ASCII visualization of the entire program IR to stdout.
pub fn visualize_program_ir(program_ir: &ProgramIR) {
    let mut output = String::new();

    // globals
    if !program_ir.globals.is_empty() {
        writeln!(output, "╔══════════════════════════════════════════╗").unwrap();
        writeln!(output, "║          Global Declarations             ║").unwrap();
        writeln!(output, "╚══════════════════════════════════════════╝").unwrap();
        for global in &program_ir.globals {
            writeln!(output, "  {}", format_global_decl(global)).unwrap();
        }
    }

    // sort function names for deterministic output
    let mut func_names: Vec<&String> = program_ir.functions.keys().collect();
    func_names.sort();

    for name in func_names {
        let func = &program_ir.functions[name];
        visualize_function_ir(&mut output, func);
    }

    print!("{}", output);
}

fn visualize_function_ir(output: &mut String, func: &FunctionIR) {
    let params_str = func
        .params
        .iter()
        .map(|p| format_value_id(p))
        .collect::<Vec<_>>()
        .join(", ");

    let header = format!(
        "Function: {}({}) -> {}",
        func.name.0,
        params_str,
        format_type(&func.ret_ty)
    );
    let rule_len = header.len().max(44);

    writeln!(output).unwrap();
    writeln!(output, "{}", "═".repeat(rule_len)).unwrap();
    writeln!(output, "{}", header).unwrap();
    writeln!(output, "{}", "═".repeat(rule_len)).unwrap();

    // collect successor edges per block for the summary
    let edges = collect_edges(func);

    for block in &func.blocks {
        writeln!(output).unwrap();
        render_block(output, block, &func.values);
    }

    // edge summary
    writeln!(output).unwrap();
    writeln!(output, "  Edge summary:").unwrap();
    for block in &func.blocks {
        let bid = block.id;
        if let Some(succs) = edges.get(&bid) {
            for (label, target) in succs {
                writeln!(output, "    B{} ──{}──► B{}", bid.0, label, target.0).unwrap();
            }
        }
    }
}

/// Build a map from each BlockId to its labelled successor edges.
fn collect_edges(func: &FunctionIR) -> HashMap<BlockId, Vec<(String, BlockId)>> {
    let mut edges: HashMap<BlockId, Vec<(String, BlockId)>> = HashMap::new();
    for block in &func.blocks {
        let succs = match &block.term {
            Terminator::Br { target, .. } => vec![("".to_string(), *target)],
            Terminator::CBr {
                then_bb, else_bb, ..
            } => vec![(" T ".to_string(), *then_bb), (" F ".to_string(), *else_bb)],
            _ => vec![],
        };
        if !succs.is_empty() {
            edges.insert(block.id, succs);
        }
    }
    edges
}

// ─────────────────────────────────────────────
// Block rendering
// ─────────────────────────────────────────────

fn render_block(output: &mut String, block: &BasicBlock, values: &HashMap<ValueId, ValueInfo>) {
    let mut body_lines: Vec<String> = Vec::new();

    // phi nodes
    if let Some(mem_phi) = &block.mem_in {
        body_lines.push(format_phi(mem_phi));
    }
    for phi in &block.phis {
        body_lines.push(format_phi(phi));
    }

    // instructions
    for instr in &block.instrs {
        body_lines.push(format_instr(instr, values));
    }

    let term_line = format_terminator(&block.term);

    // box width
    let block_label = format!("B{}", block.id.0);
    let content_max = body_lines
        .iter()
        .map(|l| l.len())
        .chain(std::iter::once(term_line.len()))
        .max()
        .unwrap_or(0);
    let box_width = content_max.max(block_label.len() + 4).max(20);

    // top border
    let pad = box_width - block_label.len() - 1;
    writeln!(output, "  ┌─ {} {}┐", block_label, "─".repeat(pad)).unwrap();

    // body
    for line in &body_lines {
        writeln!(output, "  │ {:<width$} │", line, width = box_width).unwrap();
    }

    // separator before terminator (only if there was body content)
    if !body_lines.is_empty() {
        writeln!(output, "  ├{}┤", "╌".repeat(box_width + 2)).unwrap();
    }

    // terminator
    writeln!(output, "  │ {:<width$} │", term_line, width = box_width).unwrap();

    // bottom border
    writeln!(output, "  └{}┘", "─".repeat(box_width + 2)).unwrap();

    // edge arrows
    match &block.term {
        Terminator::Br { target, .. } => {
            writeln!(output, "      └────► B{}", target.0).unwrap();
        }
        Terminator::CBr {
            then_bb, else_bb, ..
        } => {
            writeln!(output, "      ├─ T ─► B{}", then_bb.0).unwrap();
            writeln!(output, "      └─ F ─► B{}", else_bb.0).unwrap();
        }
        Terminator::Ret { .. } | Terminator::RetVoid { .. } => {
            writeln!(output, "      └────► return").unwrap();
        }
        Terminator::Unreachable => {
            writeln!(output, "      └── unreachable").unwrap();
        }
    }
}

// ─────────────────────────────────────────────
// Formatting helpers
// ─────────────────────────────────────────────

fn format_value_id(v: &ValueId) -> String {
    format!("%v{}", v.0)
}

fn format_type(ty: &Type) -> String {
    match ty {
        Type::I1 => "i1".into(),
        Type::I8 => "i8".into(),
        Type::I32 => "i32".into(),
        Type::I64 => "i64".into(),
        Type::Ptr(inner) => format!("ptr<{}>", format_type(inner)),
        Type::Mem => "mem".into(),
        Type::Void => "void".into(),
        Type::None => "none".into(),
    }
}

fn format_const_value(cv: &ConstValue) -> String {
    match cv {
        ConstValue::I1(b) => format!("{}", b),
        ConstValue::I32(i) => format!("{}", i),
        ConstValue::I64(l) => format!("{}L", l),
    }
}

fn format_phi(phi: &Phi) -> String {
    let incomings: Vec<String> = phi
        .incomings
        .iter()
        .map(|(bid, vid)| format!("[B{}: {}]", bid.0, format_value_id(vid)))
        .collect();
    format!(
        "{}:{} = phi {}",
        format_value_id(&phi.result),
        format_type(&phi.ty),
        incomings.join(", ")
    )
}

fn format_instr(instr: &Instr, values: &HashMap<ValueId, ValueInfo>) -> String {
    let results_str = if instr.results.is_empty() {
        String::new()
    } else {
        let parts: Vec<String> = instr
            .results
            .iter()
            .map(|v| {
                let ty_str = values
                    .get(v)
                    .map(|info| format_type(&info.ty))
                    .unwrap_or_else(|| "?".into());
                format!("{}:{}", format_value_id(v), ty_str)
            })
            .collect();
        format!("{} = ", parts.join(", "))
    };

    let kind_str = format_instr_kind(&instr.kind);
    format!("{}{}", results_str, kind_str)
}

fn format_instr_kind(kind: &InstrKind) -> String {
    match kind {
        InstrKind::Const(cv) => {
            let ty = match cv {
                ConstValue::I1(_) => "i1",
                ConstValue::I32(_) => "i32",
                ConstValue::I64(_) => "i64",
            };
            format!("const_{} {}", ty, format_const_value(cv))
        }
        InstrKind::Copy { src } => format!("copy {}", format_value_id(src)),
        InstrKind::BinOp { op, ty, lhs, rhs } => {
            let op_name = match op {
                BinOp::Add => "add",
                BinOp::Sub => "sub",
                BinOp::Mul => "mul",
                BinOp::SDiv => "sdiv",
                BinOp::SRem => "srem",
            };
            format!(
                "{}_{} {}, {}",
                op_name,
                format_type(ty),
                format_value_id(lhs),
                format_value_id(rhs)
            )
        }
        InstrKind::UnOp { op, ty, arg } => {
            let op_name = match op {
                UnOp::Neg => "neg",
                UnOp::Not => "not",
            };
            format!("{}_{} {}", op_name, format_type(ty), format_value_id(arg))
        }
        InstrKind::ICmp { pred, ty, lhs, rhs } => {
            let pred_name = match pred {
                ICmpPred::Eq => "eq",
                ICmpPred::Ne => "ne",
                ICmpPred::Lt => "lt",
                ICmpPred::Le => "le",
                ICmpPred::Gt => "gt",
                ICmpPred::Ge => "ge",
            };
            format!(
                "icmp_{}_{} {}, {}",
                pred_name,
                format_type(ty),
                format_value_id(lhs),
                format_value_id(rhs)
            )
        }
        InstrKind::Cast { kind, src } => {
            let cast_name = match kind {
                CastKind::I32ToI64 => "i32_to_i64",
                CastKind::I64ToI32 => "i64_to_i32",
                CastKind::I1ToI32 => "i1_to_i32",
                CastKind::I1ToI64 => "i1_to_i64",
            };
            format!("cast_{} {}", cast_name, format_value_id(src))
        }
        InstrKind::GlobalAddr { sym, ty } => {
            format!("global_addr @{} : {}", sym.0, format_type(ty))
        }
        InstrKind::GlobalArrayAddr { sym, elem_ty } => {
            format!("global_array_addr @{} : {}", sym.0, format_type(elem_ty))
        }
        InstrKind::GlobalStrAddr { sym } => format!("global_str_addr @{}", sym.0),
        InstrKind::ElemAddr {
            elem_ty,
            base,
            index,
        } => format!(
            "elem_addr {}, {}, {}",
            format_type(elem_ty),
            format_value_id(base),
            format_value_id(index)
        ),
        InstrKind::Load { ty, mem, addr } => format!(
            "load {}, {}, {}",
            format_type(ty),
            format_value_id(mem),
            format_value_id(addr)
        ),
        InstrKind::Store {
            ty,
            mem,
            addr,
            value,
        } => format!(
            "store {}, {}, {}, {}",
            format_type(ty),
            format_value_id(mem),
            format_value_id(addr),
            format_value_id(value)
        ),
        InstrKind::Call {
            mem,
            callee,
            args,
            ret_ty,
        } => {
            let args_str = args
                .iter()
                .map(|a| format_value_id(a))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "call @{}({}) : {} [mem {}]",
                callee.0,
                args_str,
                format_type(ret_ty),
                format_value_id(mem)
            )
        }
        InstrKind::CallImport {
            mem,
            callee,
            args,
            ret_ty,
        } => {
            let args_str = args
                .iter()
                .map(|a| format_value_id(a))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "call_import @{}({}) : {} [mem {}]",
                callee.0,
                args_str,
                format_type(ret_ty),
                format_value_id(mem)
            )
        }
    }
}

fn format_terminator(term: &Terminator) -> String {
    match term {
        Terminator::Br { mem, target } => {
            format!("br B{} [mem {}]", target.0, format_value_id(mem))
        }
        Terminator::CBr {
            mem,
            cond,
            then_bb,
            else_bb,
        } => format!(
            "cbr {}, B{}, B{} [mem {}]",
            format_value_id(cond),
            then_bb.0,
            else_bb.0,
            format_value_id(mem)
        ),
        Terminator::RetVoid { mem } => format!("ret void [mem {}]", format_value_id(mem)),
        Terminator::Ret { mem, value } => {
            format!(
                "ret {} [mem {}]",
                format_value_id(value),
                format_value_id(mem)
            )
        }
        Terminator::Unreachable => "unreachable".into(),
    }
}

fn format_global_decl(global: &GlobalDecl) -> String {
    match &global.kind {
        GlobalKind::GlobalStr { bytes } => {
            let printable: String = bytes
                .iter()
                .take_while(|&&b| b != 0)
                .map(|&b| b as u8 as char)
                .collect();
            format!("@{} = str \"{}\"", global.sym.0, printable)
        }
        GlobalKind::GlobalScalar { ty, init } => {
            let init_str = init
                .as_ref()
                .map(|v| format!(" = {}", format_const_value(v)))
                .unwrap_or_default();
            format!("@{} : {}{}", global.sym.0, format_type(ty), init_str)
        }
        GlobalKind::GlobalArray { elem_ty, len, init } => {
            let init_str = init
                .as_ref()
                .map(|vals| {
                    let parts: Vec<String> = vals.iter().map(format_const_value).collect();
                    format!(" = [{}]", parts.join(", "))
                })
                .unwrap_or_default();
            format!(
                "@{} : {}[{}]{}",
                global.sym.0,
                format_type(elem_ty),
                len,
                init_str
            )
        }
    }
}
