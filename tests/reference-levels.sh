#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
reference=${LEAN4LEAN_REFERENCE:-"$root/_tmp/lean4lean-reference"}
expected=bce3448115f7819fc12d647fadd3bb090666637e
if [[ ! -d "$reference" ]]; then
  mkdir -p "$(dirname "$reference")"
  git clone https://github.com/digama0/lean4lean "$reference"
  git -C "$reference" checkout "$expected"
fi
actual=$(git -C "$reference" rev-parse HEAD)
if [[ "$actual" != "$expected" ]]; then
  echo "Reference revision mismatch: expected $expected, found $actual" >&2
  exit 1
fi
mkdir -p "$root/tests/generated"
(cd "$reference" && lake build Lean4Lean.Level Lean4Lean.Tests.Level)
(cd "$reference" && lake env lean --run "$root/tests/level.lean") > "$root/tests/generated/levels.txt"
"$root/bin/level-test" < "$root/tests/generated/levels.txt"
