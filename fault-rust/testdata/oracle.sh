#!/usr/bin/env bash
# Regenerate expected.smt2 files from the Go oracle compiler.
# Usage: ./oracle.sh [fixture_name]
# If no argument, regenerates all fixtures.
# Requires: fault_bin built at repo root (go build -o fault_bin .)

set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
FAULT_BIN="$REPO_ROOT/fault_bin"

if [ ! -x "$FAULT_BIN" ]; then
    echo "Error: fault_bin not found at $FAULT_BIN"
    echo "Build it first: cd $REPO_ROOT && go build -o fault_bin ."
    exit 1
fi

generate_one() {
    local dir="$1"
    local name
    name="$(basename "$dir")"

    local input=""
    if [ -f "$dir/input.fspec" ]; then
        input="$dir/input.fspec"
    elif [ -f "$dir/input.fsystem" ]; then
        input="$dir/input.fsystem"
    else
        return 0
    fi

    echo "Generating expected.smt2 for $name ..."
    "$FAULT_BIN" -m smt -f "$input" > "$dir/expected.smt2" 2>/dev/null
    if [ $? -ne 0 ]; then
        echo "  WARNING: oracle failed for $name (may be expected for badspecs)"
        rm -f "$dir/expected.smt2"
    fi
}

if [ $# -ge 1 ]; then
    target="$SCRIPT_DIR/$1"
    if [ -d "$target" ]; then
        generate_one "$target"
    else
        echo "Error: fixture directory not found: $target"
        exit 1
    fi
else
    for dir in "$SCRIPT_DIR"/*/; do
        [ -d "$dir" ] && generate_one "$dir"
    done
fi

echo "Done."
