#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
reference=${LEAN4LEAN_REFERENCE:-"$root/_tmp/lean4lean-reference"}
expected=bce3448115f7819fc12d647fadd3bb090666637e
actual=$(git -C "$reference" rev-parse HEAD)
if [[ "$actual" != "$expected" ]]; then
  echo "Reference revision mismatch: expected $expected, found $actual" >&2
  exit 1
fi
mkdir -p "$root/tests/generated"
(cd "$reference" && lake env lean --run "$root/tests/nat.lean") > "$root/tests/generated/nats-lean.txt"
"$root/bin/nat-test" < "$root/tests/generated/nats-lean.txt"
