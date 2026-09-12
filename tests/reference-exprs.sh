#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
reference=${LEAN4LEAN_REFERENCE:-"$root/_tmp/lean4lean-reference"}
expected=bce3448115f7819fc12d647fadd3bb090666637e
if [[ $(git -C "$reference" rev-parse HEAD) != "$expected" ]]; then
  echo "The expression oracle requires lean4lean revision $expected." >&2
  exit 1
fi
mkdir -p "$root/tests/generated"
(cd "$reference" && lake build Lean4Lean.Instantiate)
(cd "$reference" && lake env lean --run "$root/tests/expr.lean") > "$root/tests/generated/exprs.txt"
"$root/bin/expr-test" < "$root/tests/generated/exprs.txt"
