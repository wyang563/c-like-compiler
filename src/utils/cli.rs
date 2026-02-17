/**
 * A generic command-line interface for 6.035 compilers.  This class
 * provides command-line parsing for student projects.  It recognizes
 * the required <tt>-target</tt>, <tt>-debug</tt>, <tt>-opt</tt>, and
 * <tt>-o</tt> switches, and generates a name for input and output
 * files.
 *
 * @author 6.1100 Staff, last updated January 2024
 */
use clap::Parser;
use std::collections::HashSet;

#[derive(Clone, clap::ValueEnum, Debug)]
pub enum CompilerAction {
    Default,
    Scan,
    Parse,
    Inter,
    Assembly,
}

/// Individual optimization passes.
///
/// Names for use with `-O`:
///   `cse`  — Common subexpression elimination
///   `cp`   — Copy propagation
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Optimization {
    /// Common subexpression elimination
    Cse,
    /// Copy propagation
    Cp,
}

impl Optimization {
    /// All available optimizations.
    pub fn all() -> Vec<Optimization> {
        vec![Optimization::Cse, Optimization::Cp]
    }

    pub fn from_str(s: &str) -> Option<Optimization> {
        match s {
            "cse" => Some(Optimization::Cse),
            "cp" => Some(Optimization::Cp),
            _ => None,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Optimization::Cse => "cse",
            Optimization::Cp => "cp",
        }
    }
}

/// Parse the raw `-O` strings into an active set of optimizations.
///
/// Supported syntax (comma-separated, no spaces):
///   `-O cse`          — enable cse only
///   `-O cp,cse`       — enable cp and cse
///   `-O all`          — enable all optimizations
///   `-O all,-cse`     — enable all except cse
///
/// A leading `-` on a token *disables* that optimization from the set.
pub fn parse_optimizations(opts: &[String]) -> HashSet<Optimization> {
    let mut active: HashSet<Optimization> = HashSet::new();

    for token in opts {
        if token == "all" {
            for o in Optimization::all() {
                active.insert(o);
            }
        } else if let Some(name) = token.strip_prefix('-') {
            if let Some(o) = Optimization::from_str(name) {
                active.remove(&o);
            } else {
                eprintln!("Warning: unknown optimization '{}' (ignored)", name);
            }
        } else {
            if let Some(o) = Optimization::from_str(token) {
                active.insert(o);
            } else {
                eprintln!("Warning: unknown optimization '{}' (ignored)", token);
            }
        }
    }

    active
}

/// Code generation backend selection.
#[derive(Clone, clap::ValueEnum, Debug, PartialEq)]
pub enum CodegenBackend {
    /// Register-allocated codegen — efficient stack layout (codegen.rs)
    Reg,
    /// Naive codegen with no register allocation (codegen_no_reg.rs)
    #[value(name = "no-reg")]
    NoReg,
}

#[derive(Parser, Debug)]
pub struct Args {
    /// Compile to the given stage
    #[clap(short, long, value_enum, default_value_t=CompilerAction::Default, value_name = "stage")]
    pub target: CompilerAction,

    /// Write output to file
    #[clap(short, long, value_name = "outname")]
    pub output: Option<std::path::PathBuf>,

    /// Optimizations to enable. Comma-separated list of: cse, cp, all.
    /// Prefix a name with '-' to disable it (e.g. -O all,-cse).
    #[clap(
        short = 'O',
        long = "opt",
        value_delimiter = ',',
        value_name = "opt,..",
        allow_hyphen_values = true
    )]
    pub opt: Vec<String>,

    /// Code generation backend
    #[clap(long = "backend", value_enum, default_value_t = CodegenBackend::Reg)]
    pub backend: CodegenBackend,

    /// Print debugging information
    #[arg(short, long, default_value_t = false)]
    pub debug: bool,

    /// Decaf source file
    pub input: std::path::PathBuf,
}

pub fn parse() -> Args {
    Args::parse()
}
