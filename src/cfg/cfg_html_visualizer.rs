use super::cfg_visualizer::{
    collect_edges, format_global_decl, format_instr, format_phi, format_terminator, format_type,
};
use super::three_address_code::*;
use std::collections::{HashMap, VecDeque};
use std::fmt::Write;
use std::fs;

// ─────────────────────────────────────────────
// Layout constants
// ─────────────────────────────────────────────

const CHAR_W: f64 = 6.6; // monospace char width at font-size 11px
const CODE_LINE_H: f64 = 16.0;
const BLOCK_PAD_TOP: f64 = 8.0; // top padding inside block
const BLOCK_PAD_BOT: f64 = 18.0; // bottom padding (extra room for text descenders)
const BLOCK_PAD_X: f64 = 10.0; // horizontal padding inside block
const HEADER_H: f64 = 22.0; // height for block label header area
const GAP_AFTER_HEADER: f64 = 6.0; // gap between header separator and body
const TERM_SEP_SPACE: f64 = 10.0; // space around dashed separator before terminator
const H_GAP: f64 = 80.0; // horizontal gap between blocks in same layer
const V_GAP: f64 = 70.0; // vertical gap between layers (edge routing space)
const SVG_PAD: f64 = 60.0;
const ARROW_SIZE: f64 = 10.0;
const MIN_BLOCK_W: f64 = 130.0;
const BACK_EDGE_MARGIN: f64 = 70.0; // extra horizontal space for back-edge curves

// ─────────────────────────────────────────────
// Block content & sizing
// ─────────────────────────────────────────────

struct BlockContent {
    body_lines: Vec<String>,
    term_line: String,
    w: f64,
    h: f64,
}

fn compute_block_content(block: &BasicBlock, values: &HashMap<ValueId, ValueInfo>) -> BlockContent {
    let mut body_lines = Vec::new();

    if let Some(mem_phi) = &block.mem_in {
        body_lines.push(format_phi(mem_phi, values));
    }
    for phi in &block.phis {
        body_lines.push(format_phi(phi, values));
    }
    for instr in &block.instrs {
        body_lines.push(format_instr(instr, values));
    }

    let term_line = format_terminator(&block.term, values);

    let label = format!("B{}", block.id.0);
    let max_chars = body_lines
        .iter()
        .chain(std::iter::once(&term_line))
        .map(|l| l.len())
        .chain(std::iter::once(label.len() + 2))
        .max()
        .unwrap_or(10);

    let w = f64::max(MIN_BLOCK_W, max_chars as f64 * CHAR_W + BLOCK_PAD_X * 2.0);

    let body_h = body_lines.len() as f64 * CODE_LINE_H;
    let term_sep = if body_lines.is_empty() {
        0.0
    } else {
        TERM_SEP_SPACE
    };
    let h =
        BLOCK_PAD_TOP + HEADER_H + GAP_AFTER_HEADER + body_h + term_sep + CODE_LINE_H + BLOCK_PAD_BOT;

    BlockContent {
        body_lines,
        term_line,
        w,
        h,
    }
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

// ─────────────────────────────────────────────
// Layer assignment via BFS
// ─────────────────────────────────────────────

fn assign_layers(func: &FunctionIR) -> HashMap<BlockId, usize> {
    let mut layers: HashMap<BlockId, usize> = HashMap::new();
    if func.blocks.is_empty() {
        return layers;
    }

    let entry = func.blocks[0].id;
    let mut queue = VecDeque::new();
    queue.push_back(entry);
    layers.insert(entry, 0);

    let edges = collect_edges(func);

    while let Some(bid) = queue.pop_front() {
        let cur_layer = layers[&bid];
        if let Some(succs) = edges.get(&bid) {
            for (_label, target) in succs {
                if !layers.contains_key(target) {
                    layers.insert(*target, cur_layer + 1);
                    queue.push_back(*target);
                }
            }
        }
    }

    let max_layer = layers.values().copied().max().unwrap_or(0);
    for block in &func.blocks {
        layers.entry(block.id).or_insert(max_layer + 1);
    }

    layers
}

// ─────────────────────────────────────────────
// Layout computation (variable-sized blocks)
// ─────────────────────────────────────────────

struct BlockLayout {
    x: f64,
    y: f64,
    w: f64,
    h: f64,
}

fn compute_layout(
    func: &FunctionIR,
    contents: &HashMap<BlockId, BlockContent>,
) -> HashMap<BlockId, BlockLayout> {
    let layers = assign_layers(func);

    let max_layer = layers.values().copied().max().unwrap_or(0);
    let mut layer_blocks: Vec<Vec<BlockId>> = vec![vec![]; max_layer + 1];
    for block in &func.blocks {
        layer_blocks[layers[&block.id]].push(block.id);
    }

    // cumulative Y positions based on per-layer max height
    let mut layer_y: Vec<f64> = Vec::new();
    let mut cum_y = 0.0;
    for blocks in &layer_blocks {
        layer_y.push(cum_y);
        let max_h = blocks
            .iter()
            .map(|bid| contents.get(bid).map(|c| c.h).unwrap_or(40.0))
            .fold(0.0_f64, f64::max);
        cum_y += max_h + V_GAP;
    }

    let mut positions: HashMap<BlockId, BlockLayout> = HashMap::new();

    for (layer_idx, blocks) in layer_blocks.iter().enumerate() {
        let widths: Vec<f64> = blocks
            .iter()
            .map(|bid| contents.get(bid).map(|c| c.w).unwrap_or(MIN_BLOCK_W))
            .collect();
        let total_w: f64 =
            widths.iter().sum::<f64>() + (blocks.len() as f64 - 1.0).max(0.0) * H_GAP;
        let start_x = -total_w / 2.0;
        let mut cur_x = start_x;

        for (i, bid) in blocks.iter().enumerate() {
            let w = widths[i];
            let h = contents.get(bid).map(|c| c.h).unwrap_or(40.0);
            positions.insert(
                *bid,
                BlockLayout {
                    x: cur_x,
                    y: layer_y[layer_idx],
                    w,
                    h,
                },
            );
            cur_x += w + H_GAP;
        }
    }

    positions
}

// ─────────────────────────────────────────────
// Variable declarations tracking
// ─────────────────────────────────────────────

/// One row in the def-use chain panel.
struct DefUseRow {
    display_name: String, // e.g. "%v3«x»"
    ty_str: String,
    def_str: String,        // "[i5]" or "(param)"
    uses: Vec<String>,      // ["[i8]", "[i12]"]
    is_named: bool,         // true if the value has an org_name
}

fn collect_def_use_rows(func: &FunctionIR) -> Vec<DefUseRow> {
    let mut rows: Vec<(u32, DefUseRow)> = func
        .values
        .iter()
        .filter(|(_, info)| {
            info.ty != Type::Mem && info.ty != Type::Void && info.ty != Type::None
        })
        .map(|(vid, info)| {
            let display_name = if info.org_name.is_empty() {
                format!("%v{}", vid.0)
            } else {
                format!("%v{}  «{}»", vid.0, info.org_name)
            };
            let ty_str = format_type(&info.ty);
            let def_str = match info.declared_by {
                Some(iid) => format!("[i{}]", iid.0),
                None => "(param)".to_string(),
            };
            let uses: Vec<String> = info
                .use_chain
                .iter()
                .map(|iid| format!("[i{}]", iid.0))
                .collect();
            let is_named = !info.org_name.is_empty();
            (
                vid.0,
                DefUseRow {
                    display_name,
                    ty_str,
                    def_str,
                    uses,
                    is_named,
                },
            )
        })
        .collect();

    rows.sort_by_key(|(id, _)| *id);
    rows.into_iter().map(|(_, row)| row).collect()
}

// ─────────────────────────────────────────────
// SVG rendering
// ─────────────────────────────────────────────

fn render_function_svg(func: &FunctionIR) -> String {
    let mut contents: HashMap<BlockId, BlockContent> = HashMap::new();
    for block in &func.blocks {
        contents.insert(block.id, compute_block_content(block, &func.values));
    }

    let positions = compute_layout(func, &contents);
    let layers = assign_layers(func);
    let edges = collect_edges(func);

    if positions.is_empty() {
        return String::new();
    }

    // compute SVG viewport
    let min_x = positions
        .values()
        .map(|p| p.x)
        .fold(f64::INFINITY, f64::min);
    let max_x = positions
        .values()
        .map(|p| p.x + p.w)
        .fold(f64::NEG_INFINITY, f64::max);
    let max_y = positions
        .values()
        .map(|p| p.y + p.h)
        .fold(f64::NEG_INFINITY, f64::max);

    let svg_w = (max_x - min_x) + SVG_PAD * 2.0 + BACK_EDGE_MARGIN;
    let svg_h = max_y + SVG_PAD * 2.0;
    let offset_x = -min_x + SVG_PAD + BACK_EDGE_MARGIN; // margin on left for back-edge curves
    let offset_y = SVG_PAD;

    let mut svg = String::new();
    writeln!(
        svg,
        r#"<svg width="{w}" height="{h}" viewBox="0 0 {w} {h}" xmlns="http://www.w3.org/2000/svg">"#,
        w = svg_w,
        h = svg_h
    )
    .unwrap();

    // arrow marker definitions
    writeln!(svg, r#"  <defs>"#).unwrap();
    for (id, color) in [
        ("arrow-default", "#cdd6f4"),
        ("arrow-true", "#a6e3a1"),
        ("arrow-false", "#f38ba8"),
    ] {
        writeln!(
            svg,
            r#"    <marker id="{id}" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="{sz}" markerHeight="{sz}" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="{color}"/></marker>"#,
            id = id,
            sz = ARROW_SIZE,
            color = color,
        )
        .unwrap();
    }
    writeln!(svg, r#"  </defs>"#).unwrap();

    // ── render edges FIRST (behind blocks) ──
    for block in &func.blocks {
        let Some(succs) = edges.get(&block.id) else {
            continue;
        };
        let from_pos = &positions[&block.id];
        let num_succs = succs.len();

        for (edge_idx, (label, target)) in succs.iter().enumerate() {
            let to_pos = &positions[target];

            let (color, marker) = match label.trim() {
                "T" => ("#a6e3a1", "url(#arrow-true)"),
                "F" => ("#f38ba8", "url(#arrow-false)"),
                _ => ("#cdd6f4", "url(#arrow-default)"),
            };

            let from_layer = layers.get(&block.id).copied().unwrap_or(0);
            let to_layer = layers.get(target).copied().unwrap_or(0);

            if to_layer < from_layer {
                // True back edge (target is on an earlier layer): curve LEFT
                let dash = r#" stroke-dasharray="6,4""#;
                let from_left = from_pos.x + offset_x;
                let from_mid_y = from_pos.y + offset_y + from_pos.h / 2.0;
                let to_left = to_pos.x + offset_x;
                let to_mid_y = to_pos.y + offset_y + to_pos.h / 2.0;
                let ctrl_x = f64::min(from_left, to_left) - BACK_EDGE_MARGIN + 10.0;

                let path = format!(
                    "M {fx},{fy} C {cx},{fy} {cx},{ty} {tx},{ty}",
                    fx = from_left,
                    fy = from_mid_y,
                    cx = ctrl_x,
                    ty = to_mid_y,
                    tx = to_left,
                );

                // dark outline
                writeln!(
                    svg,
                    r##"  <path d="{path}" fill="none" stroke="#1e1e2e" stroke-width="6" stroke-linecap="round"{dash}/>"##,
                    path = path,
                    dash = dash,
                )
                .unwrap();
                // colored stroke
                writeln!(
                    svg,
                    r#"  <path d="{path}" fill="none" stroke="{color}" stroke-width="2.5" marker-end="{marker}"{dash}/>"#,
                    path = path,
                    color = color,
                    marker = marker,
                    dash = dash,
                )
                .unwrap();

                // edge label
                if !label.trim().is_empty() {
                    let lx = ctrl_x - 16.0;
                    let ly = (from_mid_y + to_mid_y) / 2.0;
                    writeln!(
                        svg,
                        r##"  <rect x="{rx}" y="{ry}" width="16" height="16" rx="3" fill="#1e1e2e" stroke="{color}" stroke-width="1"/>"##,
                        rx = lx - 3.0,
                        ry = ly - 12.0,
                        color = color,
                    )
                    .unwrap();
                    writeln!(
                        svg,
                        r##"  <text x="{lx}" y="{ly}" fill="{color}" font-family="monospace" font-size="11" font-weight="bold" text-anchor="middle">{label}</text>"##,
                        lx = lx + 5.0,
                        ly = ly,
                        color = color,
                        label = label.trim(),
                    )
                    .unwrap();
                }
            } else if to_layer == from_layer {
                // Same-layer edge: route horizontally between blocks
                let from_cx = from_pos.x + offset_x + from_pos.w / 2.0;
                let to_cx = to_pos.x + offset_x + to_pos.w / 2.0;

                let (fx, fy, tx, ty);
                if to_cx > from_cx {
                    // target is to the right
                    fx = from_pos.x + offset_x + from_pos.w;
                    fy = from_pos.y + offset_y + from_pos.h / 2.0;
                    tx = to_pos.x + offset_x;
                    ty = to_pos.y + offset_y + to_pos.h / 2.0;
                } else {
                    // target is to the left
                    fx = from_pos.x + offset_x;
                    fy = from_pos.y + offset_y + from_pos.h / 2.0;
                    tx = to_pos.x + offset_x + to_pos.w;
                    ty = to_pos.y + offset_y + to_pos.h / 2.0;
                }

                let mid_x = (fx + tx) / 2.0;
                let path = format!(
                    "M {fx},{fy} C {mx},{fy} {mx},{ty} {tx},{ty}",
                    fx = fx,
                    fy = fy,
                    mx = mid_x,
                    ty = ty,
                    tx = tx,
                );

                // dark outline
                writeln!(
                    svg,
                    r##"  <path d="{path}" fill="none" stroke="#1e1e2e" stroke-width="6" stroke-linecap="round"/>"##,
                    path = path,
                )
                .unwrap();
                // colored stroke
                writeln!(
                    svg,
                    r#"  <path d="{path}" fill="none" stroke="{color}" stroke-width="2.5" marker-end="{marker}"/>"#,
                    path = path,
                    color = color,
                    marker = marker,
                )
                .unwrap();

                // edge label near source
                if !label.trim().is_empty() {
                    let lx = fx + if to_cx > from_cx { 8.0 } else { -24.0 };
                    let ly = fy - 10.0;
                    writeln!(
                        svg,
                        r##"  <rect x="{rx}" y="{ry}" width="16" height="16" rx="3" fill="#1e1e2e" stroke="{color}" stroke-width="1"/>"##,
                        rx = lx - 3.0,
                        ry = ly - 12.0,
                        color = color,
                    )
                    .unwrap();
                    writeln!(
                        svg,
                        r##"  <text x="{lx}" y="{ly}" fill="{color}" font-family="monospace" font-size="11" font-weight="bold" text-anchor="middle">{label}</text>"##,
                        lx = lx + 5.0,
                        ly = ly,
                        color = color,
                        label = label.trim(),
                    )
                    .unwrap();
                }
            } else {
                // Forward edge: bezier from bottom of source to top of target
                let from_x = if num_succs == 2 {
                    let frac = if edge_idx == 0 { 0.35 } else { 0.65 };
                    from_pos.x + offset_x + from_pos.w * frac
                } else {
                    from_pos.x + offset_x + from_pos.w / 2.0
                };
                let from_y = from_pos.y + offset_y + from_pos.h;

                let to_x = to_pos.x + offset_x + to_pos.w / 2.0;
                let to_y = to_pos.y + offset_y;

                // S-curve through the gap between layers
                let mid_y = (from_y + to_y) / 2.0;
                let path = format!(
                    "M {fx},{fy} C {fx},{my} {tx},{my} {tx},{ty}",
                    fx = from_x,
                    fy = from_y,
                    my = mid_y,
                    tx = to_x,
                    ty = to_y,
                );

                // dark outline
                writeln!(
                    svg,
                    r##"  <path d="{path}" fill="none" stroke="#1e1e2e" stroke-width="6" stroke-linecap="round"/>"##,
                    path = path,
                )
                .unwrap();
                // colored stroke
                writeln!(
                    svg,
                    r#"  <path d="{path}" fill="none" stroke="{color}" stroke-width="2.5" marker-end="{marker}"/>"#,
                    path = path,
                    color = color,
                    marker = marker,
                )
                .unwrap();

                // edge label near source
                if !label.trim().is_empty() {
                    let lx = from_x + 8.0;
                    let ly = from_y + 16.0;
                    writeln!(
                        svg,
                        r##"  <rect x="{rx}" y="{ry}" width="16" height="16" rx="3" fill="#1e1e2e" stroke="{color}" stroke-width="1"/>"##,
                        rx = lx - 3.0,
                        ry = ly - 12.0,
                        color = color,
                    )
                    .unwrap();
                    writeln!(
                        svg,
                        r##"  <text x="{lx}" y="{ly}" fill="{color}" font-family="monospace" font-size="11" font-weight="bold" text-anchor="middle">{label}</text>"##,
                        lx = lx + 5.0,
                        ly = ly,
                        color = color,
                        label = label.trim(),
                    )
                    .unwrap();
                }
            }
        }
    }

    // ── render blocks ON TOP (so they occlude edges passing behind them) ──
    for block in &func.blocks {
        let pos = &positions[&block.id];
        let content = &contents[&block.id];
        let bx = pos.x + offset_x;
        let by = pos.y + offset_y;
        let bw = pos.w;
        let bh = pos.h;
        let label = format!("B{}", block.id.0);

        writeln!(svg, r#"  <g class="cfg-block">"#).unwrap();

        // block background
        writeln!(
            svg,
            r##"    <rect x="{x}" y="{y}" width="{w}" height="{h}" rx="6" ry="6" fill="#313244" stroke="#585b70" stroke-width="1.5"/>"##,
            x = bx, y = by, w = bw, h = bh,
        )
        .unwrap();

        // header label (centered, blue)
        let label_baseline = by + BLOCK_PAD_TOP + 14.0;
        writeln!(
            svg,
            r##"    <text x="{tx}" y="{ty}" text-anchor="middle" fill="#89b4fa" font-family="monospace" font-size="13" font-weight="bold">{label}</text>"##,
            tx = bx + bw / 2.0,
            ty = label_baseline,
            label = label,
        )
        .unwrap();

        // solid separator after header
        let sep_y = by + BLOCK_PAD_TOP + HEADER_H;
        writeln!(
            svg,
            r##"    <line x1="{x1}" y1="{sy}" x2="{x2}" y2="{sy}" stroke="#585b70" stroke-width="0.5"/>"##,
            x1 = bx + 4.0,
            x2 = bx + bw - 4.0,
            sy = sep_y,
        )
        .unwrap();

        // body lines (white text)
        let mut text_y = sep_y + GAP_AFTER_HEADER + 12.0;
        for line in &content.body_lines {
            writeln!(
                svg,
                r##"    <text x="{tx}" y="{ty}" fill="#cdd6f4" font-family="monospace" font-size="11">{text}</text>"##,
                tx = bx + BLOCK_PAD_X,
                ty = text_y,
                text = html_escape(line),
            )
            .unwrap();
            text_y += CODE_LINE_H;
        }

        // dashed separator before terminator (only if body content exists)
        if !content.body_lines.is_empty() {
            let dsep_y = text_y - CODE_LINE_H + CODE_LINE_H + TERM_SEP_SPACE / 2.0;
            writeln!(
                svg,
                r##"    <line x1="{x1}" y1="{sy}" x2="{x2}" y2="{sy}" stroke="#585b70" stroke-width="0.5" stroke-dasharray="4,3"/>"##,
                x1 = bx + 4.0,
                x2 = bx + bw - 4.0,
                sy = dsep_y,
            )
            .unwrap();
            text_y = dsep_y + TERM_SEP_SPACE / 2.0 + 12.0;
        }

        // terminator line (yellow text)
        writeln!(
            svg,
            r##"    <text x="{tx}" y="{ty}" fill="#f9e2af" font-family="monospace" font-size="11">{text}</text>"##,
            tx = bx + BLOCK_PAD_X,
            ty = text_y,
            text = html_escape(&content.term_line),
        )
        .unwrap();

        writeln!(svg, r#"  </g>"#).unwrap();
    }

    writeln!(svg, r#"</svg>"#).unwrap();
    svg
}

// ─────────────────────────────────────────────
// Full HTML document
// ─────────────────────────────────────────────

pub fn generate_html_cfg(program_ir: &ProgramIR, path: &str) {
    let mut html = String::new();

    writeln!(html, r#"<!DOCTYPE html>"#).unwrap();
    writeln!(html, r#"<html lang="en">"#).unwrap();
    writeln!(html, r#"<head>"#).unwrap();
    writeln!(html, r#"<meta charset="utf-8"/>"#).unwrap();
    writeln!(html, r#"<title>CFG Visualization</title>"#).unwrap();
    writeln!(html, r#"<style>"#).unwrap();
    writeln!(
        html,
        r#"
body {{
    background: #1e1e2e;
    color: #cdd6f4;
    font-family: 'Segoe UI', system-ui, sans-serif;
    margin: 0;
    padding: 20px;
}}
h1 {{
    color: #cba6f7;
    font-size: 1.4em;
    margin-bottom: 8px;
}}
h2 {{
    color: #89b4fa;
    font-size: 1.1em;
    margin: 0;
    cursor: pointer;
}}
h3 {{
    color: #f9e2af;
    font-size: 0.95em;
    margin: 0 0 12px 0;
}}
details {{
    margin-bottom: 24px;
}}
details summary {{
    list-style: none;
    padding: 8px 12px;
    background: #181825;
    border-radius: 6px;
    border: 1px solid #313244;
}}
details summary::-webkit-details-marker {{
    display: none;
}}
details summary::before {{
    content: '\25B6';
    display: inline-block;
    margin-right: 8px;
    transition: transform 0.15s;
    color: #585b70;
}}
details[open] summary::before {{
    transform: rotate(90deg);
}}
.function-content {{
    display: flex;
    gap: 20px;
}}
.svg-container {{
    flex: 1;
    overflow-x: auto;
    padding: 16px 0;
}}
.side-panel {{
    width: 300px;
    flex-shrink: 0;
    background: #181825;
    border: 1px solid #313244;
    border-radius: 6px;
    padding: 16px;
    max-height: 800px;
    overflow-y: auto;
}}
.var-list {{
    font-family: monospace;
    font-size: 12px;
}}
.var-item {{
    padding: 6px 8px;
    margin-bottom: 4px;
    background: #1e1e2e;
    border-radius: 4px;
    border-left: 3px solid #89b4fa;
}}
.var-name {{
    color: #cdd6f4;
    font-weight: bold;
}}
.var-type {{
    color: #a6e3a1;
    font-size: 11px;
}}
.var-instr {{
    color: #f9e2af;
    font-size: 11px;
}}
.var-uses {{
    color: #cba6f7;
    font-size: 11px;
    margin-top: 2px;
    word-break: break-all;
}}
.var-uses-empty {{
    color: #585b70;
    font-size: 11px;
    font-style: italic;
    margin-top: 2px;
}}
.var-item-named {{
    border-left-color: #f9e2af;
}}
.globals {{
    background: #181825;
    border: 1px solid #313244;
    border-radius: 6px;
    padding: 12px 16px;
    margin-bottom: 20px;
    font-family: monospace;
    font-size: 13px;
    white-space: pre;
}}
"#
    )
    .unwrap();
    writeln!(html, r#"</style>"#).unwrap();
    writeln!(html, r#"</head>"#).unwrap();
    writeln!(html, r#"<body>"#).unwrap();
    writeln!(html, r#"<h1>Control Flow Graph</h1>"#).unwrap();

    // globals
    if !program_ir.globals.is_empty() {
        writeln!(html, r#"<div class="globals">"#).unwrap();
        for global in &program_ir.globals {
            writeln!(html, "{}", html_escape(&format_global_decl(global))).unwrap();
        }
        writeln!(html, r#"</div>"#).unwrap();
    }

    // functions
    let mut func_names: Vec<&String> = program_ir.functions.keys().collect();
    func_names.sort();

    for name in func_names {
        let func = &program_ir.functions[name];
        let params_str = func
            .params
            .iter()
            .map(|p| {
                let info = func.values.get(p);
                let ty_str = info
                    .map(|i| format_type(&i.ty))
                    .unwrap_or_else(|| "?".into());
                format!("{}: {}", p.0, ty_str)
            })
            .collect::<Vec<_>>()
            .join(", ");

        let header = format!(
            "{}({}) -> {}",
            func.name.0,
            params_str,
            format_type(&func.ret_ty)
        );

        writeln!(html, r#"<details open>"#).unwrap();
        writeln!(
            html,
            r#"<summary><h2>{}</h2></summary>"#,
            html_escape(&header)
        )
        .unwrap();

        writeln!(html, r#"<div class="function-content">"#).unwrap();

        // Side panel: def-use chains for all allocatable values
        let def_use_rows = collect_def_use_rows(func);
        writeln!(html, r#"<div class="side-panel">"#).unwrap();
        writeln!(html, r#"<h3>Def-Use Chains</h3>"#).unwrap();
        writeln!(html, r#"<div class="var-list">"#).unwrap();

        if def_use_rows.is_empty() {
            writeln!(
                html,
                r#"<div style="color: #585b70; font-style: italic;">No values</div>"#
            )
            .unwrap();
        } else {
            for row in &def_use_rows {
                // Named variables get a highlighted border colour.
                let item_class = if row.is_named {
                    r#"var-item var-item-named"#
                } else {
                    "var-item"
                };
                writeln!(html, r#"<div class="{}">"#, item_class).unwrap();
                writeln!(
                    html,
                    r#"<div class="var-name">{}</div>"#,
                    html_escape(&row.display_name)
                )
                .unwrap();
                writeln!(
                    html,
                    r#"<div class="var-type">type: {}</div>"#,
                    html_escape(&row.ty_str)
                )
                .unwrap();
                writeln!(
                    html,
                    r#"<div class="var-instr">def: {}</div>"#,
                    html_escape(&row.def_str)
                )
                .unwrap();
                if row.uses.is_empty() {
                    writeln!(
                        html,
                        r#"<div class="var-uses-empty">uses: —</div>"#
                    )
                    .unwrap();
                } else {
                    writeln!(
                        html,
                        r#"<div class="var-uses">uses: {}</div>"#,
                        html_escape(&row.uses.join(", "))
                    )
                    .unwrap();
                }
                writeln!(html, r#"</div>"#).unwrap();
            }
        }

        writeln!(html, r#"</div>"#).unwrap(); // end var-list
        writeln!(html, r#"</div>"#).unwrap(); // end side-panel

        // SVG container
        writeln!(html, r#"<div class="svg-container">"#).unwrap();
        let svg = render_function_svg(func);
        writeln!(html, "{}", svg).unwrap();
        writeln!(html, r#"</div>"#).unwrap(); // end svg-container

        writeln!(html, r#"</div>"#).unwrap(); // end function-content
        writeln!(html, r#"</details>"#).unwrap();
    }

    writeln!(html, r#"</body>"#).unwrap();
    writeln!(html, r#"</html>"#).unwrap();

    fs::write(path, &html).unwrap_or_else(|e| {
        eprintln!("Error writing HTML CFG to {}: {}", path, e);
    });

    eprintln!("CFG visualization written to {}", path);
}
