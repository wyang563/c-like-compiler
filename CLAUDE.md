# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Rust implementation of a Decaf compiler for MIT's 6.1100 course. The compiler translates Decaf source files (.dcf) through multiple compilation phases: scanning, parsing, semantic analysis, intermediate representation generation, and assembly code generation.

## Build and Test Commands

### Build
```bash
cargo build          # Build debug version
cargo build --release  # Build optimized version
cargo check          # Fast syntax/type check without codegen
cargo clippy         # Run linter
```

### Running the Compiler
```bash
# General usage
target/debug/rust-compiler --target <stage> <input.dcf> [--output <file>] [--debug]

# Stages (use with --target flag)
--target scan      # Tokenize input (scanner phase)
--target parse     # Parse and build AST (parser phase)
--target inter     # Semantic analysis and interpretation
--target assembly  # Generate assembly code
```

### Testing
```bash
# Test individual phases using provided scripts
./tests/scanner.sh [public]      # Run scanner tests
./tests/parser.sh [public]       # Run parser tests
./tests/semantics.sh [public]    # Run semantics tests

# Test directories are organized by phase:
# - phase1-scanner/  - tokenization tests
# - phase1-parser/   - AST construction tests
# - phase2-semantics/ - type checking, scoping tests (legal/ and illegal/ subdirs)
# - phase3-codegen/  - code generation tests
# - phase4-dataflow/ - optimization tests
# - phase5-derby/    - final integration tests
```

## Architecture

### Compilation Pipeline
The compiler follows a classic multi-phase architecture:

1. **Scanner** (`src/scanner/`) - Lexical analysis
   - Tokenizes input Decaf source files
   - Defined in `scanner.rs` with token constants in `constants.rs`

2. **Parser** (`src/parser/`) - Syntax analysis
   - Builds Abstract Syntax Tree (AST) from tokens
   - AST node definitions: `AST.rs` (defines `ASTNode` enum with ~20 variants)
   - Parser implementation: `parser.rs`
   - Visitor pattern: `visitor.rs` (defines `Visitor` trait for AST traversal)
   - Pretty printing: `parser_printer.rs`

3. **Semantics** (`src/semantics/`) - Semantic analysis
   - Type checking and scope resolution
   - `semantics.rs`: `Interpreter` struct implements `Visitor` trait
   - `symbol_table.rs`: Symbol table with scoped entries (VarEntry, MethodEntry, ArrayEntry, ImportEntry)
   - Tracks scoping with parent/child scope indices
   - Validates Decaf semantic rules (no undeclared variables, type compatibility, etc.)

4. **CFG/IR** (`src/cfg/`) - Intermediate representation
   - `three_address_code.rs`: Defines IR structures (BasicBlock, Instr, ProgramIR, FunctionIR)
   - `ssa_cfg_compiler.rs`: SSA-form CFG compiler using visitor pattern
     - Implements `SSA_CFG_Compiler` struct with symbol table integration
     - Tracks loop contexts for break/continue
     - Generates ValueIds and BlockIds for SSA form
   - `cfg_visualizer.rs`: Visualization utilities for control flow graphs

5. **Assembler** (`src/assembler/`) - Code generation
   - Translates IR to target assembly code

### Visitor Pattern Usage
The visitor pattern is central to this compiler's architecture:
- `Visitor` trait in `src/parser/visitor.rs` defines visit methods for each AST node type
- All AST nodes implement `accept()` method that calls appropriate visitor method
- Semantic analysis (`Interpreter`), CFG compilation (`SSA_CFG_Compiler`), and other passes implement `Visitor`
- Key visitor methods: `visit_expression`, `visit_method_decl`, `visit_block`, `visit_if_statement`, etc.
- The main dispatcher is `visit_ast_node()` which pattern matches on `ASTNode` variants

### Symbol Table Design
- Hierarchical scope structure with parent/child relationships tracked by indices
- `SymbolTable` contains vector of `Table` scopes
- Each `Table` has `HashMap<String, Entry>` for name lookups
- Entry types: VarEntry (variables), MethodEntry (functions), ArrayEntry (arrays), ImportEntry (imports)
- Type system: `Type` enum includes Int, Long, Bool, Void, Array types

### Recent Work
Based on git history:
- Refactored literal constant handling in `visit_expression`
- Implemented identifier variable reading changes in `visit_identifier`
- Created CFG visualizer for debugging control flow
- Initial implementation of `visit_if_statement` for conditional control flow
- Modified `visit_method_decl` and `visit_block` for scope management

## CLI Structure
- Uses `clap` crate with derive macros for argument parsing (`src/utils/cli.rs`)
- `CompilerAction` enum defines compilation stages
- `Optimization` enum placeholder for future optimizations
- Main entry point: `src/main.rs` dispatches to appropriate phase handler

## Code Conventions
- Follow Rust naming: `snake_case` for functions/variables, `CamelCase` for types/structs
- Use `#[allow(dead_code)]` sparingly - prefer fixing warnings
- AST nodes are typically `Box`ed to reduce stack size
- Visitor methods take `&mut self` and node references (`&AST::Node`)
- Error handling: semantics phase collects errors in `Vec<String>` and sets `correct: bool` flag
