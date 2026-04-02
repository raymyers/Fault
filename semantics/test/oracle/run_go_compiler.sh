#!/bin/bash
# Oracle test harness: run the Go Fault compiler and capture output
# Usage: ./run_go_compiler.sh <fspec_path> [mode: ast|ir|smt]
#
# Builds the compiler if needed, then runs it on the given file.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FAULT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
FAULT_BIN="$FAULT_ROOT/fault_bin"
MODE="${2:-smt}"

# Build if needed
if [ ! -f "$FAULT_BIN" ] || [ "$FAULT_ROOT/main.go" -nt "$FAULT_BIN" ]; then
    echo "Building Fault compiler..." >&2
    (cd "$FAULT_ROOT" && go build -o fault_bin .) >&2
fi

# Run
"$FAULT_BIN" -m "$MODE" -f "$1"
