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

const BLOCK_W: f64 = 180.0;
const BLOCK_H: f64 = 50.0;
const H_GAP: f64 = 60.0;
const V_GAP: f64 = 80.0;
const SVG_PAD: f64 = 40.0;
const ARROW_SIZE: f64 = 8.0;

// ─────────────────────────────────────────────
// Block layout position
// ─────────────────────────────────────────────

struct BlockLayout {
    x: f64,
    y: f64,
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

    // build successor map
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

    // assign any unreachable blocks to max_layer + 1
    let max_layer = layers.values().copied().max().unwrap_or(0);
    for block in &func.blocks {
        layers.entry(block.id).or_insert(max_layer + 1);
    }

    layers
}

fn compute_layout(func: &FunctionIR) -> HashMap<BlockId, BlockLayout> {
    let layers = assign_layers(func);

    // group blocks by layer, preserving block order within each layer
    let max_layer = layers.values().copied().max().unwrap_or(0);
    let mut layer_blocks: Vec<Vec<BlockId>> = vec![vec![]; max_layer + 1];
    for block in &func.blocks {
        let layer = layers[&block.id];
        layer_blocks[layer].push(block.id);
    }

    let mut positions: HashMap<BlockId, BlockLayout> = HashMap::new();

    for (layer_idx, blocks) in layer_blocks.iter().enumerate() {
        let count = blocks.len() as f64;
        let total_w = count * BLOCK_W + (count - 1.0).max(0.0) * H_GAP;
        let start_x = -total_w / 2.0;

        for (i, bid) in blocks.iter().enumerate() {
            let x = start_x + i as f64 * (BLOCK_W + H_GAP);
            let y = layer_idx as f64 * (BLOCK_H + V_GAP);
            positions.insert(*bid, BlockLayout { x, y });
        }
    }

    positions
}

// ─────────────────────────────────────────────
// Detect back-edges (target layer <= source layer)
// ─────────────────────────────────────────────

fn is_back_edge(layers: &HashMap<BlockId, usize>, from: BlockId, to: BlockId) -> bool {
    let from_layer = layers.get(&from).copied().unwrap_or(0);
    let to_layer = layers.get(&to).copied().unwrap_or(0);
    to_layer <= from_layer
}

// ─────────────────────────────────────────────
// Block content as HTML-escaped text lines
// ─────────────────────────────────────────────

fn block_content_lines(block: &BasicBlock, values: &HashMap<ValueId, ValueInfo>) -> Vec<String> {
    let mut lines = Vec::new();

    if let Some(mem_phi) = &block.mem_in {
        lines.push(format_phi(mem_phi, values));
    }
    for phi in &block.phis {
        lines.push(format_phi(phi, values));
    }
    for instr in &block.instrs {
        lines.push(format_instr(instr, values));
    }
    lines.push("--- terminator ---".to_string());
    lines.push(format_terminator(&block.term, values));

    lines
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

// ─────────────────────────────────────────────
// SVG generation per function
// ─────────────────────────────────────────────

fn render_function_svg(func: &FunctionIR) -> String {
    let positions = compute_layout(func);
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
        .map(|p| p.x + BLOCK_W)
        .fold(f64::NEG_INFINITY, f64::max);
    let max_y = positions
        .values()
        .map(|p| p.y + BLOCK_H)
        .fold(f64::NEG_INFINITY, f64::max);

    let svg_w = (max_x - min_x) + SVG_PAD * 2.0;
    let svg_h = max_y + SVG_PAD * 2.0;
    let offset_x = -min_x + SVG_PAD;
    let offset_y = SVG_PAD;

    let mut svg = String::new();
    writeln!(
        svg,
        r#"<svg width="{w}" height="{h}" viewBox="0 0 {w} {h}" xmlns="http://www.w3.org/2000/svg">"#,
        w = svg_w,
        h = svg_h
    )
    .unwrap();

    // arrow marker defs
    writeln!(svg, r#"  <defs>"#).unwrap();
    for (id, color) in [
        ("arrow-default", "#cdd6f4"),
        ("arrow-true", "#a6e3a1"),
        ("arrow-false", "#f38ba8"),
    ] {
        writeln!(
            svg,
            r#"    <marker id="{id}" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="{sz}" markerHeight="{sz}" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="{color}"/></marker>"#,
            id = id,
            sz = ARROW_SIZE,
            color = color,
        )
        .unwrap();
    }
    writeln!(svg, r#"  </defs>"#).unwrap();

    // draw edges first (behind blocks)
    for block in &func.blocks {
        if let Some(succs) = edges.get(&block.id) {
            let from_pos = &positions[&block.id];
            let from_cx = from_pos.x + offset_x + BLOCK_W / 2.0;
            let from_bot = from_pos.y + offset_y + BLOCK_H;

            for (label, target) in succs {
                let to_pos = &positions[target];
                let to_cx = to_pos.x + offset_x + BLOCK_W / 2.0;
                let to_top = to_pos.y + offset_y;

                let (color, marker) = match label.trim() {
                    "T" => ("#a6e3a1", "url(#arrow-true)"),
                    "F" => ("#f38ba8", "url(#arrow-false)"),
                    _ => ("#cdd6f4", "url(#arrow-default)"),
                };

                let back = is_back_edge(&layers, block.id, *target);
                let dash = if back {
                    r#" stroke-dasharray="6,4""#
                } else {
                    ""
                };

                if back {
                    // draw a curved back-edge: go out to the right side
                    let from_right = from_pos.x + offset_x + BLOCK_W;
                    let from_mid_y = from_pos.y + offset_y + BLOCK_H / 2.0;
                    let to_right = to_pos.x + offset_x + BLOCK_W;
                    let to_mid_y = to_pos.y + offset_y + BLOCK_H / 2.0;
                    let ctrl_x = f64::max(from_right, to_right) + 50.0;
                    writeln!(
                        svg,
                        r#"  <path d="M {fx},{fy} C {cx},{fy} {cx},{ty} {tx},{ty}" fill="none" stroke="{color}" stroke-width="1.5" marker-end="{marker}"{dash}/>"#,
                        fx = from_right,
                        fy = from_mid_y,
                        cx = ctrl_x,
                        ty = to_mid_y,
                        tx = to_right,
                        color = color,
                        marker = marker,
                        dash = dash,
                    )
                    .unwrap();
                } else {
                    // straight/angled line from bottom-center to top-center
                    writeln!(
                        svg,
                        r#"  <line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{color}" stroke-width="1.5" marker-end="{marker}"{dash}/>"#,
                        x1 = from_cx,
                        y1 = from_bot,
                        x2 = to_cx,
                        y2 = to_top,
                        color = color,
                        marker = marker,
                        dash = dash,
                    )
                    .unwrap();
                }
            }
        }
    }

    // draw blocks
    for block in &func.blocks {
        let pos = &positions[&block.id];
        let x = pos.x + offset_x;
        let y = pos.y + offset_y;
        let label = format!("B{}", block.id.0);

        let content_lines = block_content_lines(block, &func.values);
        let tooltip_html: String = content_lines
            .iter()
            .map(|l| html_escape(l))
            .collect::<Vec<_>>()
            .join("<br/>");

        // block group with hover events
        writeln!(
            svg,
            r#"  <g class="cfg-block" onmouseenter="showTip(evt, this)" onmouseleave="hideTip(evt, this)">"#,
        )
        .unwrap();

        // rect
        writeln!(
            svg,
            r##"    <rect x="{x}" y="{y}" width="{w}" height="{h}" rx="6" ry="6" fill="#313244" stroke="#585b70" stroke-width="1.5"/>"##,
            x = x,
            y = y,
            w = BLOCK_W,
            h = BLOCK_H,
        )
        .unwrap();

        // label text
        writeln!(
            svg,
            r##"    <text x="{tx}" y="{ty}" text-anchor="middle" dominant-baseline="central" fill="#cdd6f4" font-family="monospace" font-size="14" font-weight="bold">{label}</text>"##,
            tx = x + BLOCK_W / 2.0,
            ty = y + BLOCK_H / 2.0,
            label = label,
        )
        .unwrap();

        // hidden tooltip data attribute
        writeln!(
            svg,
            r#"    <rect class="hit" x="{x}" y="{y}" width="{w}" height="{h}" fill="transparent" data-tooltip="{tip}"/>"#,
            x = x,
            y = y,
            w = BLOCK_W,
            h = BLOCK_H,
            tip = html_escape(&tooltip_html.replace("\"", "&quot;")),
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
.svg-container {{
    overflow-x: auto;
    padding: 16px 0;
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
#tooltip {{
    position: fixed;
    display: none;
    background: #181825;
    border: 1px solid #585b70;
    border-radius: 6px;
    padding: 10px 14px;
    font-family: monospace;
    font-size: 12px;
    color: #cdd6f4;
    line-height: 1.6;
    pointer-events: none;
    z-index: 1000;
    max-width: 600px;
    box-shadow: 0 4px 16px rgba(0,0,0,0.4);
}}
"#
    )
    .unwrap();
    writeln!(html, r#"</style>"#).unwrap();
    writeln!(html, r#"</head>"#).unwrap();
    writeln!(html, r#"<body>"#).unwrap();
    writeln!(html, r#"<h1>Control Flow Graph</h1>"#).unwrap();

    // tooltip div
    writeln!(html, r#"<div id="tooltip"></div>"#).unwrap();

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
        writeln!(html, r#"<div class="svg-container">"#).unwrap();

        let svg = render_function_svg(func);
        writeln!(html, "{}", svg).unwrap();

        writeln!(html, r#"</div>"#).unwrap();
        writeln!(html, r#"</details>"#).unwrap();
    }

    // inline JS for tooltip
    writeln!(html, r#"<script>"#).unwrap();
    writeln!(
        html,
        r#"
const tip = document.getElementById('tooltip');
function showTip(evt, g) {{
    const hit = g.querySelector('.hit');
    if (!hit) return;
    const raw = hit.getAttribute('data-tooltip');
    if (!raw) return;
    tip.innerHTML = raw;
    tip.style.display = 'block';
    positionTip(evt);
}}
function hideTip(evt, g) {{
    tip.style.display = 'none';
}}
document.addEventListener('mousemove', function(e) {{
    if (tip.style.display === 'block') positionTip(e);
}});
function positionTip(e) {{
    let x = e.clientX + 16;
    let y = e.clientY + 16;
    const tw = tip.offsetWidth;
    const th = tip.offsetHeight;
    if (x + tw > window.innerWidth - 8) x = e.clientX - tw - 8;
    if (y + th > window.innerHeight - 8) y = e.clientY - th - 8;
    tip.style.left = x + 'px';
    tip.style.top = y + 'px';
}}
"#
    )
    .unwrap();
    writeln!(html, r#"</script>"#).unwrap();

    writeln!(html, r#"</body>"#).unwrap();
    writeln!(html, r#"</html>"#).unwrap();

    fs::write(path, &html).unwrap_or_else(|e| {
        eprintln!("Error writing HTML CFG to {}: {}", path, e);
    });

    eprintln!("CFG visualization written to {}", path);
}
