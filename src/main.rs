mod cfg;
mod parser;
mod scanner;
mod semantics;
mod utils;

fn get_writer(output: &Option<std::path::PathBuf>) -> Box<dyn std::io::Write> {
    match output {
        Some(path) => Box::new(std::fs::File::create(path.as_path()).unwrap()),
        None => Box::new(std::io::stdout()),
    }
}

fn main() {
    let args = utils::cli::parse();
    let _input = std::fs::read_to_string(&args.input).expect("Filename is incorrect.");

    if args.debug {
        eprintln!(
            "Filename: {:?}\nDebug: {:?}\nOptimizations: {:?}\nOutput File: {:?}\nTarget: {:?}",
            args.input, args.debug, args.opt, args.output, args.target
        );
    }

    // Use writeln!(writer, "template string") to write to stdout or file.
    let writer = get_writer(&args.output);
    match args.target {
        utils::cli::CompilerAction::Default => {
            panic!("Invalid target");
        }
        utils::cli::CompilerAction::Scan => {
            scanner::scanner::scan(&args.input, writer);
        }
        utils::cli::CompilerAction::Parse => {
            parser::parser::parse(&args.input, writer, args.debug);
        }
        utils::cli::CompilerAction::Inter => {
            semantics::semantics::interpret(&args.input, writer, args.debug);
        }
        utils::cli::CompilerAction::Assembly => {}
    }
}
