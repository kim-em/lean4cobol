#!/usr/bin/env bash
# Register this worktree in a local arena and run its already-built streams.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
arena=${LEAN_KERNEL_ARENA:-"$root/_tmp/arena"}
if [[ ! -f "$arena/lka.py" ]]; then
  echo "Set LEAN_KERNEL_ARENA to a Lean Kernel Arena checkout with built tests." >&2
  exit 3
fi
python3 - "$root" "$arena" <<'PY'
import json
import shutil
from pathlib import Path
import sys
root, arena = map(Path, sys.argv[1:])
# lka copies local sources recursively. Stage only source inputs, so an arena
# checkout beneath this repository cannot recursively copy its own build tree.
staging = root / '_tmp/arena-source'
if staging.exists():
    shutil.rmtree(staging)
staging.mkdir(parents=True)
for name in ('src', 'tests', 'scripts'):
    shutil.copytree(root / name, staging / name,
                    ignore=shutil.ignore_patterns('__pycache__', 'generated'))
for name in ('Makefile', 'LICENSE', 'NOTICE', 'README.md'):
    shutil.copy2(root / name, staging / name)
config = (root / 'arena/lean4cobol.yaml').read_text()
config = config.replace('dir: ..', 'dir: ' + json.dumps(str(staging)))
(arena / 'checkers/lean4cobol.yaml').write_text(config)
PY
cd "$arena"
uv run lka.py build-checker lean4cobol
uv run lka.py run --checker lean4cobol "$@"
