#!/usr/bin/env python3
"""Compare actual checker verdicts; strict mode also fails on any decline."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def run(executable, path, timeout, reference=False):
    args = [str(executable)] + (['--import'] if reference else []) + [str(path)]
    start = time.monotonic()
    try:
        p = subprocess.run(args, capture_output=True, timeout=timeout)
        return {'exit': p.returncode, 'seconds': round(time.monotonic()-start, 6),
                'stderr': p.stderr.decode(errors='replace')[-4000:]}
    except subprocess.TimeoutExpired:
        return {'exit': 'timeout', 'seconds': timeout, 'stderr': ''}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--suite', type=Path, default=ROOT / '_tmp/arena/_build/tests/tutorial')
    ap.add_argument('--checker', type=Path, default=ROOT / 'bin/lean4cobol')
    ap.add_argument('--reference', type=Path, default=ROOT / '_tmp/lean4lean-reference/.lake/build/bin/lean4lean')
    ap.add_argument('--output', type=Path, default=ROOT / 'tests/generated/differential.json')
    ap.add_argument('--timeout', type=int, default=120)
    ap.add_argument('--allow-declines', action='store_true', help='Development only: still report declines, but do not fail for them.')
    args = ap.parse_args()
    paths = sorted(args.suite.resolve().rglob('*.ndjson'))
    if not paths:
        ap.error(f'No NDJSON streams under {args.suite}')
    rows = []
    counts = Counter()
    for path in paths:
        checker = run(args.checker.resolve(), path, args.timeout)
        reference = run(args.reference.resolve(), path, args.timeout, reference=True)
        if checker['exit'] not in (0, 1, 2) or reference['exit'] not in (0, 1, 2):
            status = 'error'
        elif checker['exit'] == 2:
            status = 'declined'
        elif checker['exit'] == reference['exit']:
            status = 'match'
        else:
            status = 'mismatch'
        counts[status] += 1
        rows.append({'test': str(path.relative_to(args.suite.resolve())),
                     'checker': checker, 'reference': reference, 'status': status})
        if status in ('error', 'mismatch'):
            print(f"{status}: {path.name}: COBOL {checker['exit']}, Lean {reference['exit']}", flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({'summary': dict(counts), 'results': rows}, indent=2) + '\n')
    print(json.dumps(dict(counts), sort_keys=True))
    return int(bool(counts['error'] or counts['mismatch'] or (counts['declined'] and not args.allow_declines)))


if __name__ == '__main__':
    raise SystemExit(main())
