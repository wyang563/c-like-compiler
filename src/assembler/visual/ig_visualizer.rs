// Visualizers for the interference graph.
//
// Two outputs:
//   print_interference_graphs  – ASCII summary to stdout (all functions)
//   generate_html_ig           – single HTML file; one <details> section per function

use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use std::fs;

use crate::assembler::interference_graph::{
    build_interference_graph, InterferenceGraph, NodeId, PhysReg, ALL_REGS, CALLER_SAVED,
};
use crate::assembler::liveness::compute_liveness;
use crate::cfg::three_address_code::{FunctionIR, ProgramIR, Type, ValueId};

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

fn node_label(n: NodeId, func: &FunctionIR) -> String {
    match n {
        NodeId::Physical(pr) => phys_short(pr).to_string(),
        NodeId::Virtual(v) => virtual_label(v, func),
    }
}

fn virtual_label(v: ValueId, func: &FunctionIR) -> String {
    match func.values.get(&v) {
        Some(info) if !info.org_name.is_empty() => format!("%v{}«{}»", v.0, info.org_name),
        _ => format!("%v{}", v.0),
    }
}

fn phys_short(pr: PhysReg) -> &'static str {
    match pr {
        PhysReg::Rax => "rax",
        PhysReg::Rcx => "rcx",
        PhysReg::Rdx => "rdx",
        PhysReg::Rsi => "rsi",
        PhysReg::Rdi => "rdi",
        PhysReg::R8 => "r8",
        PhysReg::R9 => "r9",
        PhysReg::R10 => "r10",
        PhysReg::R11 => "r11",
        PhysReg::Rbx => "rbx",
        PhysReg::R12 => "r12",
        PhysReg::R13 => "r13",
        PhysReg::R14 => "r14",
        PhysReg::R15 => "r15",
    }
}

fn type_str(v: ValueId, func: &FunctionIR) -> String {
    match func.values.get(&v) {
        Some(info) => format!("{:?}", info.ty),
        None => "?".to_string(),
    }
}

fn is_caller_saved(pr: PhysReg) -> bool {
    CALLER_SAVED.contains(&pr)
}

/// Sort virtual nodes by ValueId for deterministic output.
fn sorted_virtual_nodes(g: &InterferenceGraph, func: &FunctionIR) -> Vec<ValueId> {
    let mut vs: Vec<ValueId> = g
        .adj
        .keys()
        .filter_map(|n| match n {
            NodeId::Virtual(v) => {
                if func
                    .values
                    .get(v)
                    .map(|i| i.ty != Type::Mem && i.ty != Type::Void && i.ty != Type::None)
                    .unwrap_or(false)
                {
                    Some(*v)
                } else {
                    None
                }
            }
            NodeId::Physical(_) => None,
        })
        .collect();
    vs.sort_by_key(|v| v.0);
    vs
}

fn sorted_func_names(program_ir: &ProgramIR) -> Vec<&String> {
    let mut names: Vec<&String> = program_ir.functions.keys().collect();
    names.sort();
    names
}

// ---------------------------------------------------------------------------
// ASCII visualizer
// ---------------------------------------------------------------------------

pub fn print_interference_graphs(program_ir: &ProgramIR) {
    let mut out = String::new();
    for name in sorted_func_names(program_ir) {
        let func = &program_ir.functions[name];
        let liveness = compute_liveness(func);
        let g = build_interference_graph(func, &liveness);
        render_ascii_ig(&mut out, func, &g);
    }
    print!("{}", out);
}

fn render_ascii_ig(out: &mut String, func: &FunctionIR, g: &InterferenceGraph) {
    let virts = sorted_virtual_nodes(g, func);
    let total_edges: usize = g.adj.values().map(|s| s.len()).sum::<usize>() / 2;
    let total_copy = g.copy_related.len();

    let header = format!(
        "Interference Graph — {} (virtuals: {}, phys: {}, edges: {}, copy-related: {})",
        func.name.0,
        virts.len(),
        ALL_REGS.len(),
        total_edges,
        total_copy,
    );
    let rule = "═".repeat(header.len().max(60));

    writeln!(out).unwrap();
    writeln!(out, "{rule}").unwrap();
    writeln!(out, "{header}").unwrap();
    writeln!(out, "{rule}").unwrap();

    writeln!(out, "\n  Virtual nodes:").unwrap();
    for v in &virts {
        let vn = NodeId::Virtual(*v);
        let label = virtual_label(*v, func);
        let ty = type_str(*v, func);
        let degree = g.degree(vn);

        let mut virt_nbrs: Vec<String> = Vec::new();
        let mut phys_nbrs: Vec<String> = Vec::new();
        let mut nbr_ids: Vec<NodeId> = g.neighbors(vn).collect();
        nbr_ids.sort_by_key(|n| match n {
            NodeId::Virtual(vv) => (0u8, vv.0, 0u8),
            NodeId::Physical(pr) => (1u8, 0, *pr as u8),
        });
        for nbr in nbr_ids {
            match nbr {
                NodeId::Virtual(u) => virt_nbrs.push(virtual_label(u, func)),
                NodeId::Physical(pr) => phys_nbrs.push(phys_short(pr).to_string()),
            }
        }

        write!(out, "    {:<20} : {:<6} deg={:<3}", label, ty, degree).unwrap();
        if !virt_nbrs.is_empty() {
            write!(out, "  virt=[{}]", virt_nbrs.join(", ")).unwrap();
        }
        if !phys_nbrs.is_empty() {
            write!(out, "  phys=[{}]", phys_nbrs.join(", ")).unwrap();
        }
        writeln!(out).unwrap();
    }

    if !g.copy_related.is_empty() {
        writeln!(out, "\n  Copy-related pairs (coalescing candidates):").unwrap();
        let mut pairs: Vec<_> = g.copy_related.iter().collect();
        pairs.sort_by_key(|(a, b)| (format!("{:?}", a), format!("{:?}", b)));
        for (a, b) in pairs {
            writeln!(
                out,
                "    {} ↔ {}",
                node_label(*a, func),
                node_label(*b, func)
            )
            .unwrap();
        }
    }

    writeln!(
        out,
        "\n  Physical registers (degree = #virtuals interfering):"
    )
    .unwrap();
    let mut phys_sorted: Vec<PhysReg> = ALL_REGS.to_vec();
    phys_sorted.sort();
    for pr in &phys_sorted {
        let pn = NodeId::Physical(*pr);
        let deg = g.degree(pn);
        let kind = if is_caller_saved(*pr) {
            "caller-saved"
        } else {
            "callee-saved"
        };
        writeln!(
            out,
            "    {:<5}  ({:<12})  deg={}",
            phys_short(*pr),
            kind,
            deg
        )
        .unwrap();
    }
}

// ---------------------------------------------------------------------------
// HTML / SVG visualizer  — single file, one <details> per function
// ---------------------------------------------------------------------------

pub fn generate_html_ig(program_ir: &ProgramIR, path: &str) {
    let mut html = String::new();

    writeln!(html, "<!DOCTYPE html>").unwrap();
    writeln!(html, r#"<html lang="en">"#).unwrap();
    writeln!(html, "<head>").unwrap();
    writeln!(html, r#"<meta charset="UTF-8">"#).unwrap();
    writeln!(html, "<title>Interference Graph</title>").unwrap();
    html.push_str(HTML_STYLE);
    writeln!(html, "</head>").unwrap();
    writeln!(html, "<body>").unwrap();
    writeln!(html, "<h1>Interference Graph</h1>").unwrap();

    for name in sorted_func_names(program_ir) {
        let func = &program_ir.functions[name];
        let liveness = compute_liveness(func);
        let g = build_interference_graph(func, &liveness);
        render_function_section(&mut html, func, &g);
    }

    writeln!(html, "</body>").unwrap();
    writeln!(html, "</html>").unwrap();

    fs::write(path, &html).unwrap_or_else(|e| {
        eprintln!("Error writing interference graph HTML to {}: {}", path, e);
    });
    eprintln!("Interference graph written to {}", path);
}

/// Emit one `<details>` block for a single function.
fn render_function_section(html: &mut String, func: &FunctionIR, g: &InterferenceGraph) {
    let virts = sorted_virtual_nodes(g, func);
    let total_edges: usize = g.adj.values().map(|s| s.len()).sum::<usize>() / 2;

    let summary = format!(
        "{}  <span class=\"fn-stats\">\
         virtuals: {}&nbsp;&nbsp;edges: {}&nbsp;&nbsp;copy-related: {}</span>",
        html_escape(&func.name.0),
        virts.len(),
        total_edges,
        g.copy_related.len(),
    );

    writeln!(html, "<details open>").unwrap();
    writeln!(html, "<summary><h2>{}</h2></summary>", summary).unwrap();

    // Legend (once per section — compact)
    html.push_str("<div class=\"legend\">");
    html.push_str("<span class=\"leg caller\">caller-saved</span>");
    html.push_str("<span class=\"leg callee\">callee-saved</span>");
    html.push_str("<span class=\"leg virt\">virtual</span>");
    html.push_str("<span class=\"leg named\">named virtual</span>");
    html.push_str("<span class=\"leg edge-interf\">── interference</span>");
    html.push_str("<span class=\"leg edge-copy\">╌╌ copy-related</span>");
    html.push_str("</div>\n");

    // SVG
    html.push_str("<div class=\"svg-wrap\">\n");
    render_svg(html, func, g, &virts);
    html.push_str("</div>\n");

    // Adjacency table
    render_adj_table(html, func, g, &virts);

    // Copy-related table (if any)
    if !g.copy_related.is_empty() {
        render_copy_table(html, func, g);
    }

    writeln!(html, "</details>").unwrap();
}

fn render_svg(html: &mut String, func: &FunctionIR, g: &InterferenceGraph, virts: &[ValueId]) {
    let canvas_w: f64 = 1100.0;
    let node_r: f64 = 22.0;
    let phys_r: f64 = 18.0;
    let top_pad: f64 = 60.0;
    let phys_row_h: f64 = 60.0;
    let virt_top: f64 = top_pad + phys_row_h * 2.0 + 40.0;
    let virt_cols: usize = 8;
    let virt_col_w: f64 = (canvas_w - 40.0) / virt_cols as f64;
    let virt_row_h: f64 = 70.0;

    let virt_rows = if virts.is_empty() {
        0
    } else {
        (virts.len() + virt_cols - 1) / virt_cols
    };
    let canvas_h: f64 = virt_top + virt_rows as f64 * virt_row_h + 60.0;

    // Build position map
    let mut pos: HashMap<NodeId, (f64, f64)> = HashMap::new();

    // Caller-saved: top row
    let caller_saved: Vec<PhysReg> = CALLER_SAVED.to_vec();
    let cs_count = caller_saved.len() as f64;
    for (i, &pr) in caller_saved.iter().enumerate() {
        let cx = 40.0 + (canvas_w - 80.0) / (cs_count - 1.0) * i as f64;
        pos.insert(NodeId::Physical(pr), (cx, top_pad));
    }

    // Callee-saved: second row
    let callee_saved: Vec<PhysReg> = ALL_REGS
        .iter()
        .copied()
        .filter(|pr| !is_caller_saved(*pr))
        .collect();
    let ce_count = callee_saved.len() as f64;
    for (i, &pr) in callee_saved.iter().enumerate() {
        let cx = 80.0 + (canvas_w - 160.0) / (ce_count - 1.0).max(1.0) * i as f64;
        pos.insert(NodeId::Physical(pr), (cx, top_pad + phys_row_h));
    }

    // Virtual nodes: grid
    for (idx, &v) in virts.iter().enumerate() {
        let col = idx % virt_cols;
        let row = idx / virt_cols;
        let cx = 20.0 + virt_col_w * col as f64 + virt_col_w / 2.0;
        let cy = virt_top + row as f64 * virt_row_h + node_r + 5.0;
        pos.insert(NodeId::Virtual(v), (cx, cy));
    }

    write!(
        html,
        "<svg width=\"{canvas_w}\" height=\"{canvas_h}\" class=\"ig-svg\">\n"
    )
    .unwrap();

    // Interference edges
    let mut drawn: std::collections::HashSet<(String, String)> =
        std::collections::HashSet::new();
    for (n, neighbors) in &g.adj {
        for nbr in neighbors {
            if matches!(n, NodeId::Physical(_)) && matches!(nbr, NodeId::Physical(_)) {
                continue;
            }
            let la = format!("{:?}", n);
            let lb = format!("{:?}", nbr);
            let key = if la < lb { (la, lb) } else { (lb, la) };
            if !drawn.insert(key) {
                continue;
            }
            let (x1, y1) = match pos.get(n) {
                Some(p) => *p,
                None => continue,
            };
            let (x2, y2) = match pos.get(nbr) {
                Some(p) => *p,
                None => continue,
            };
            write!(
                html,
                "<line x1=\"{x1:.1}\" y1=\"{y1:.1}\" x2=\"{x2:.1}\" y2=\"{y2:.1}\" \
                 class=\"edge-interf\"/>\n"
            )
            .unwrap();
        }
    }

    // Copy-related edges (dashed, on top)
    let mut drawn_copy: std::collections::HashSet<(String, String)> =
        std::collections::HashSet::new();
    for (a, b) in &g.copy_related {
        let la = format!("{:?}", a);
        let lb = format!("{:?}", b);
        let key = if la < lb {
            (la.clone(), lb.clone())
        } else {
            (lb.clone(), la.clone())
        };
        if !drawn_copy.insert(key) {
            continue;
        }
        let (x1, y1) = match pos.get(a) {
            Some(p) => *p,
            None => continue,
        };
        let (x2, y2) = match pos.get(b) {
            Some(p) => *p,
            None => continue,
        };
        write!(
            html,
            "<line x1=\"{x1:.1}\" y1=\"{y1:.1}\" x2=\"{x2:.1}\" y2=\"{y2:.1}\" \
             class=\"edge-copy\"/>\n"
        )
        .unwrap();
    }

    // Physical register nodes
    for &pr in &ALL_REGS {
        let pn = NodeId::Physical(pr);
        let (cx, cy) = match pos.get(&pn) {
            Some(p) => *p,
            None => continue,
        };
        let cls = if is_caller_saved(pr) {
            "node-caller"
        } else {
            "node-callee"
        };
        let deg = g.degree(pn);
        write!(
            html,
            "<g>\
             <circle cx=\"{cx:.1}\" cy=\"{cy:.1}\" r=\"{phys_r}\" class=\"{cls}\"/>\
             <text x=\"{cx:.1}\" y=\"{:.1}\" class=\"node-label\">{}</text>\
             <text x=\"{cx:.1}\" y=\"{:.1}\" class=\"node-deg\">d={deg}</text>\
             </g>\n",
            cy + 3.5,
            phys_short(pr),
            cy + phys_r + 11.0,
        )
        .unwrap();
    }

    // Virtual nodes
    for &v in virts {
        let vn = NodeId::Virtual(v);
        let (cx, cy) = match pos.get(&vn) {
            Some(p) => *p,
            None => continue,
        };
        let deg = g.degree(vn);
        let label = match func.values.get(&v) {
            Some(info) if !info.org_name.is_empty() => format!("v{}:{}", v.0, info.org_name),
            _ => format!("v{}", v.0),
        };
        let ty = type_str(v, func);
        let named = func
            .values
            .get(&v)
            .map(|i| !i.org_name.is_empty())
            .unwrap_or(false);
        let cls = if named { "node-virt-named" } else { "node-virt" };
        write!(
            html,
            "<g>\
             <circle cx=\"{cx:.1}\" cy=\"{cy:.1}\" r=\"{node_r}\" class=\"{cls}\"/>\
             <text x=\"{cx:.1}\" y=\"{:.1}\" class=\"node-label\">{label}</text>\
             <text x=\"{cx:.1}\" y=\"{:.1}\" class=\"node-ty\">{ty}</text>\
             <text x=\"{cx:.1}\" y=\"{:.1}\" class=\"node-deg\">d={deg}</text>\
             </g>\n",
            cy + 2.0,
            cy + node_r + 11.0,
            cy + node_r + 22.0,
        )
        .unwrap();
    }

    html.push_str("</svg>\n");
}

fn render_adj_table(
    html: &mut String,
    func: &FunctionIR,
    g: &InterferenceGraph,
    virts: &[ValueId],
) {
    html.push_str("<h3>Virtual Node Details</h3>\n");
    html.push_str(
        "<table class=\"adj-table\">\
         <tr><th>Node</th><th>Type</th><th>Degree</th>\
         <th>Virtual neighbours</th><th>Physical neighbours</th></tr>\n",
    );
    for &v in virts {
        let vn = NodeId::Virtual(v);
        let label = virtual_label(v, func);
        let ty = type_str(v, func);
        let deg = g.degree(vn);

        let mut virt_nbrs: Vec<String> = Vec::new();
        let mut phys_nbrs: Vec<String> = Vec::new();
        for nbr in g.neighbors(vn) {
            match nbr {
                NodeId::Virtual(u) => virt_nbrs.push(virtual_label(u, func)),
                NodeId::Physical(pr) => phys_nbrs.push(phys_short(pr).to_string()),
            }
        }
        virt_nbrs.sort();
        phys_nbrs.sort();

        let virt_str = if virt_nbrs.is_empty() {
            "<i>—</i>".to_string()
        } else {
            virt_nbrs.join(", ")
        };
        let phys_str = if phys_nbrs.is_empty() {
            "<i>—</i>".to_string()
        } else {
            phys_nbrs.join(", ")
        };
        write!(
            html,
            "<tr><td><code>{}</code></td><td>{}</td><td>{}</td>\
             <td>{}</td><td>{}</td></tr>\n",
            html_escape(&label),
            ty,
            deg,
            virt_str,
            phys_str,
        )
        .unwrap();
    }
    html.push_str("</table>\n");
}

fn render_copy_table(html: &mut String, func: &FunctionIR, g: &InterferenceGraph) {
    html.push_str("<h3>Copy-Related Pairs (coalescing candidates)</h3>\n");
    html.push_str(
        "<table class=\"adj-table\">\
         <tr><th>Node A</th><th>Node B</th></tr>\n",
    );
    let mut pairs: Vec<_> = g.copy_related.iter().collect();
    pairs.sort_by_key(|(a, b)| (format!("{:?}", a), format!("{:?}", b)));
    for (a, b) in pairs {
        write!(
            html,
            "<tr><td><code>{}</code></td><td><code>{}</code></td></tr>\n",
            html_escape(&node_label(*a, func)),
            html_escape(&node_label(*b, func)),
        )
        .unwrap();
    }
    html.push_str("</table>\n");
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

// ---------------------------------------------------------------------------
// CSS  (matches the dark Catppuccin theme used by cfg_html_visualizer)
// ---------------------------------------------------------------------------

const HTML_STYLE: &str = r#"<style>
body {
    background: #1e1e2e;
    color: #cdd6f4;
    font-family: 'Segoe UI', system-ui, sans-serif;
    margin: 0;
    padding: 20px;
}
h1 { color: #cba6f7; font-size: 1.4em; margin-bottom: 8px; }
h2 { color: #89b4fa; font-size: 1.1em; margin: 0; cursor: pointer; }
h3 { color: #f9e2af; font-size: 0.95em; margin: 12px 0 6px; }

details { margin-bottom: 24px; }
details summary {
    list-style: none;
    padding: 8px 12px;
    background: #181825;
    border-radius: 6px;
    border: 1px solid #313244;
}
details summary::-webkit-details-marker { display: none; }
details summary::before {
    content: '\25B6';
    display: inline-block;
    margin-right: 8px;
    transition: transform 0.15s;
    color: #585b70;
}
details[open] summary::before { transform: rotate(90deg); }

.fn-stats { font-size: 0.8em; color: #a6e3a1; font-weight: normal; margin-left: 12px; }

.legend {
    display: flex; gap: 10px; flex-wrap: wrap;
    margin: 10px 0 8px; padding: 0 4px;
}
.leg {
    padding: 2px 8px; border-radius: 4px; font-size: 11px;
    font-family: monospace;
}
.leg.caller      { background: #f38ba8; color: #1e1e2e; }
.leg.callee      { background: #89b4fa; color: #1e1e2e; }
.leg.virt        { background: #313244; color: #a6e3a1; border: 1px solid #a6e3a1; }
.leg.named       { background: #313244; color: #f9e2af; border: 1px solid #f9e2af; }
.leg.edge-interf { color: #585b70; border: 1px solid #585b70; }
.leg.edge-copy   { color: #f9e2af; border: 1px dashed #f9e2af; }

.svg-wrap { overflow-x: auto; padding: 8px 0; }
.ig-svg {
    background: #181825;
    border: 1px solid #313244;
    border-radius: 6px;
    display: block;
}

.edge-interf { stroke: #45475a; stroke-width: 1.2; stroke-opacity: 0.6; }
.edge-copy   { stroke: #f9e2af; stroke-width: 1.5; stroke-dasharray: 5,3; stroke-opacity: 0.85; }

.node-caller     { fill: #f38ba8; stroke: #eba0ac; stroke-width: 1.5; }
.node-callee     { fill: #89b4fa; stroke: #74c7ec; stroke-width: 1.5; }
.node-virt       { fill: #313244; stroke: #a6e3a1; stroke-width: 1.5; }
.node-virt-named { fill: #313244; stroke: #f9e2af; stroke-width: 2; }

.node-label { font-size: 9px; text-anchor: middle; fill: #cdd6f4; font-weight: bold; }
.node-ty    { font-size: 8px; text-anchor: middle; fill: #89dceb; }
.node-deg   { font-size: 8px; text-anchor: middle; fill: #a6adc8; }

.adj-table { border-collapse: collapse; margin-top: 4px; width: 100%; font-size: 12px; font-family: monospace; }
.adj-table th, .adj-table td { border: 1px solid #313244; padding: 3px 8px; text-align: left; }
.adj-table th  { background: #313244; color: #cba6f7; }
.adj-table tr:nth-child(even) { background: #181825; }
code { color: #a6e3a1; }
</style>
"#;
