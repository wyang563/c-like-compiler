use super::super::cfg::cfg_html_visualizer::generate_html_cfg;
use super::super::cfg::cfg_visualizer::visualize_program_ir;
use super::super::cfg::ssa_cfg_compiler::compile_to_ssa_cfg;
use super::super::parser::parser::parse_file;
use super::super::semantics::semantics::interpret_file;
use super::super::utils::cli::{CodegenBackend, Optimization};
use super::ig_visualizer::{generate_html_ig, print_interference_graphs};
use super::reg_alloc::{allocate_program, Location};
use std::collections::HashSet;

pub fn assemble(
    input: &std::path::PathBuf,
    mut writer: Box<dyn std::io::Write>,
    debug: bool,
    _opts: &HashSet<Optimization>,
    backend: &CodegenBackend,
) {
    match parse_file(input) {
        Ok(ast) => {
            match interpret_file(input, debug) {
                Ok(symbol_table) => {
                    // Create SSA form CFG and eliminate phi nodes
                    let mut ssa_cfg_compiler = compile_to_ssa_cfg(ast, symbol_table);

                    // run enabled optimizations on CFG
                    ssa_cfg_compiler.remove_phis();
                    ssa_cfg_compiler.populate_use_chains();

                    // post optimization debug prints
                    if debug {
                        visualize_program_ir(&ssa_cfg_compiler.program_ir);
                        generate_html_cfg(&ssa_cfg_compiler.program_ir, "cfg_output.html");
                        print_interference_graphs(&ssa_cfg_compiler.program_ir);
                        generate_html_ig(&ssa_cfg_compiler.program_ir, "ig_output.html");
                    }

                    // Code generation
                    let asm_output = match backend {
                        CodegenBackend::Reg => {
                            // reg allocation
                            let program_alloc = allocate_program(&ssa_cfg_compiler.program_ir);
                            let mut codegen = super::codegen::CodeGenerator::new(program_alloc);
                            codegen.generate(&ssa_cfg_compiler.program_ir)
                        }
                        CodegenBackend::NoReg => {
                            let mut codegen = super::codegen_no_reg::CodeGeneratorNoReg::new();
                            codegen.generate(&ssa_cfg_compiler.program_ir)
                        }
                    };
                    write!(writer, "{}", asm_output).unwrap();
                }
                Err(e) => {
                    writeln!(writer, "Error in semantic analysis of file with the following errors reported: \n {:?}", e).unwrap();
                }
            }
        }
        Err(e) => {
            writeln!(writer, "Error parsing input file with error: {:?}", e).unwrap();
        }
    }
}
