#!/bin/bash
# Compile a Decaf source file through a chosen stage and optionally run the result.
#
# Usage: ./run.sh [options] <input.dcf>
#
# Options:
#   -t <stage>        Target stage: scan, parse, inter, assembly (default: assembly)
#   -O <opts>         Optimization flags (assembly only).
#                       Examples: -O cse        enable cse only
#                                 -O cp,cse     enable cp and cse
#                                 -O all        enable all optimizations
#                                 -O all,-cse   enable all except cse
#   --backend <b>     Codegen backend: reg (default) or no-reg  [assembly only]
#   -o <file>         Output file (scan/parse/inter: compiler output, default: stdout)
#                                 (assembly: binary name,           default: a.out)
#   -S <file>         Assembly file written by the compiler        [assembly only]
#                     (default: derived from -o, e.g. a.out -> a.s)
#   -d, --debug       Enable compiler debug output
#   -h, --help        Show this help

set -e

COMPILER="target/debug/rust-compiler"
TARGET="assembly"
BACKEND="reg"
OUTPUT=""
ASM_FILE=""
OPT_FLAGS=()
DEBUG_FLAG=""
INPUT=""

usage() {
    sed -n '2,22p' "$0" | sed 's/^# \{0,1\}//'
    exit 0
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        -t)
            TARGET="$2"; shift 2 ;;
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
        -d|--debug)
            DEBUG_FLAG="--debug"; shift ;;
        -h|--help)
            usage ;;
        -*)
            echo "Error: unknown flag: $1" >&2; exit 1 ;;
        *)
            INPUT="$1"; shift ;;
    esac
done

if [[ -z "$INPUT" ]]; then
    echo "Error: no input file specified." >&2
    usage
fi

case "$TARGET" in

    # ── Non-codegen stages: just run the compiler ──────────────────────────
    scan|parse|inter)
        COMPILER_ARGS=("--target" "$TARGET")
        [[ -n "$OUTPUT"     ]] && COMPILER_ARGS+=("-o" "$OUTPUT")
        [[ -n "$DEBUG_FLAG" ]] && COMPILER_ARGS+=("$DEBUG_FLAG")
        echo "Running stage '$TARGET' on $INPUT..."
        "$COMPILER" "${COMPILER_ARGS[@]}" "$INPUT"
        ;;

    # ── Assembly: compile -> assemble -> run ───────────────────────────────
    assembly)
        [[ -z "$OUTPUT" ]] && OUTPUT="a.out"

        # Derive the assembly filename from the binary name when not given.
        if [[ -z "$ASM_FILE" ]]; then
            ASM_FILE="${OUTPUT%.out}.s"
            [[ "$ASM_FILE" == "$OUTPUT" ]] && ASM_FILE="${OUTPUT}.s"
        fi

        # Step 1: compile Decaf -> assembly
        echo "Compiling $INPUT -> $ASM_FILE (backend=$BACKEND)..."
        COMPILER_ARGS=("--target" "assembly" "--backend" "$BACKEND")
        COMPILER_ARGS+=("${OPT_FLAGS[@]}")
        [[ -n "$DEBUG_FLAG" ]] && COMPILER_ARGS+=("$DEBUG_FLAG")
        COMPILER_ARGS+=("-o" "$ASM_FILE")
        "$COMPILER" "${COMPILER_ARGS[@]}" "$INPUT"

        # Step 2: assemble and link
        echo "Assembling $ASM_FILE -> $OUTPUT..."
        gcc "$ASM_FILE" -o "$OUTPUT" -Wl,-z,noexecstack

        # Step 3: run (allow non-zero exit from the program itself)
        echo "Running $OUTPUT..."
        echo "---"
        set +e
        "$OUTPUT"
        EXIT_CODE=$?
        set -e
        echo "---"
        echo "Exit code: $EXIT_CODE"
        ;;

    *)
        echo "Error: unknown target '$TARGET'. Valid stages: scan, parse, inter, assembly." >&2
        exit 1
        ;;
esac
