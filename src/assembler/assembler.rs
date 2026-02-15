use super::super::cfg::cfg_html_visualizer::generate_html_cfg;
use super::super::cfg::cfg_visualizer::visualize_program_ir;
use super::super::cfg::ssa_cfg_compiler::compile_to_ssa_cfg;
use super::super::parser::parser::parse_file;
use super::super::semantics::semantics::interpret_file;

pub fn assemble(input: &std::path::PathBuf, mut writer: Box<dyn std::io::Write>, debug: bool) {
    match parse_file(input) {
        Ok(ast) => {
            match interpret_file(input, debug) {
                Ok(symbol_table) => {
                    // create SSA form CFG
                    let ssa_cfg = compile_to_ssa_cfg(ast, symbol_table);
                    visualize_program_ir(&ssa_cfg);
                    generate_html_cfg(&ssa_cfg, "cfg_output.html");

                    // TODO: run optimizations on CFG

                    // code gen
                    let mut codegen = super::codegen::CodeGenerator::new();
                    let asm_output = codegen.generate(&ssa_cfg);
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
