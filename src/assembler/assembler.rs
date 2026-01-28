use super::super::semantics::semantics::interpret_file;
use super::super::parser::parser::parse_file;
use super::super::cfg::ssa_cfg_compiler::compile_to_ssa_cfg;

pub fn assemble(input: &std::path::PathBuf, mut writer: Box<dyn std::io::Write>, debug: bool) {
    match parse_file(input) {
        Ok(ast) => {
            match interpret_file(input, debug) {
                Ok(symbol_table) => {
                    // create SSA form CFG
                    let ssa_cfg = compile_to_ssa_cfg(ast, symbol_table);
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
