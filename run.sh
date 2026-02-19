#!/bin/bash
# Compile a Decaf file and run the resulting binary.
#
# Usage: ./run.sh [options] <input.dcf>
#
# Options:
#   -O <opts>         Optimization flags (e.g. -O cse, -O cp,cse, -O all, -O all,-cse)
#   --backend <b>     Codegen backend: no-reg (default) or reg
#   -o <file>         Output binary name (default: a.out)
#   -S <file>         Assembly output file (default: derived from -o)
#   -h, --help        Show this help

set -e

COMPILER="target/debug/rust-compiler"
BACKEND="no-reg"
OUTPUT="a.out"
ASM_FILE=""
OPT_FLAGS=()
INPUT=""

usage() {
    sed -n '2,12p' "$0" | sed 's/^# \{0,1\}//'
    exit 0
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case "$1" in
        -O)
            OPT_FLAGS+=("-O" "$2"); shift 2 ;;
        -O*)
            OPT_FLAGS+=("-O" "${1#-O}"); shift ;;
        --backend)
            BACKEND="$2"; shift 2 ;;
        -o)
            OUTPUT="$2"; shift 2 ;;
        -S)
            ASM_FILE="$2"; shift 2 ;;
        -h|--help)
            usage ;;
        -*)
            echo "Unknown flag: $1" >&2; exit 1 ;;
        *)
            INPUT="$1"; shift ;;
    esac
done

if [[ -z "$INPUT" ]]; then
    echo "Error: no input file specified." >&2
    usage
fi

if [[ -z "$ASM_FILE" ]]; then
    ASM_FILE="${OUTPUT%.out}.s"
    if [[ "$ASM_FILE" == "$OUTPUT" ]]; then
        ASM_FILE="${OUTPUT}.s"
    fi
fi

# Step 1: compile to assembly
echo "Compiling $INPUT -> $ASM_FILE (backend=$BACKEND)..."
"$COMPILER" --target assembly --backend "$BACKEND" "${OPT_FLAGS[@]}" "$INPUT" --output "$ASM_FILE"

# Step 2: assemble and link
echo "Assembling $ASM_FILE -> $OUTPUT..."
gcc "$ASM_FILE" -o "$OUTPUT" -Wl,-z,noexecstack

# Step 3: run (don't let a non-zero program exit code kill the script)
echo "Running $OUTPUT..."
echo "---"
set +e
"$OUTPUT"
EXIT_CODE=$?
set -e
echo "---"
echo "Exit code: $EXIT_CODE"
