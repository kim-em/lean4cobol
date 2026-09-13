#!/usr/bin/env python3
"""Compare a completed arena run with the pinned reference, reusing COBOL results.

Every built input needs a result newer than both the input and checker binary.
Declines make no assertion and are reported separately. This avoids rerunning
expensive COBOL checks merely to collect the reference verdicts.
"""
import argparse
import fnmatch
from collections import Counter
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
REVISION = 'bce3448115f7819fc12d647fadd3bb090666637e'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--arena', type=Path, default=ROOT / '_tmp/arena')
    ap.add_argument('--reference-root', type=Path, default=ROOT / '_tmp/lean4lean-reference')
    ap.add_argument('--output', type=Path, default=ROOT / 'tests/generated/arena-reference.json')
    ap.add_argument('--timeout', type=int, default=None, help='Optional reference timeout; unlimited by default')
    ap.add_argument('--exclude', nargs='*', default=[], help='Test names/globs measured separately')
    ap.add_argument('--declared-declines', nargs='*', default=[])
    args = ap.parse_args()
    revision = subprocess.check_output(['git', '-C', str(args.reference_root), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != REVISION:
        ap.error(f'reference revision is {revision}, expected {REVISION}')
    checker = args.arena / '_build/checkers/lean4cobol/src/bin/lean4cobol'
    if not checker.exists():
        ap.error('the arena checker has not been built')
    built_at = checker.stat().st_mtime_ns
    reference = args.reference_root / '.lake/build/bin/lean4lean'
    tests = {}
    for stats in sorted((args.arena / '_build/tests').rglob('*.stats.json')):
        data = json.loads(stats.read_text())
        source = stats.with_name(stats.name.removesuffix('.stats.json') + '.ndjson')
        if data['name'] in tests:
            ap.error(f'duplicate built test: {data["name"]}')
        tests[data['name']] = source
    for name in args.declared_declines:
        tests.setdefault(name, None)
    if not tests:
        ap.error('no arena tests found')
    excluded = sorted(name for name in tests if any(fnmatch.fnmatchcase(name, pat) for pat in args.exclude))
    tests = {name: source for name, source in tests.items() if name not in excluded}
    rows = []
    counts = Counter()
    for name, source in sorted(tests.items()):
        result_file = args.arena / '_results' / ('lean4cobol_' + name.replace('/', '_') + '.json')
        row = {'test': name}
        if not result_file.exists():
            row |= {'status': 'error', 'reason': 'missing arena result'}
        else:
            result = json.loads(result_file.read_text())
            row['checker'] = {k: result.get(k) for k in ['exit_code', 'status', 'wall_time', 'instructions', 'max_rss']}
            fresh_after = max(built_at, source.stat().st_mtime_ns if source and source.exists() else 0)
            if result_file.stat().st_mtime_ns < fresh_after:
                row |= {'status': 'error', 'reason': 'stale result; rerun the arena checker'}
            elif result.get('test') != name or result.get('checker') != 'lean4cobol':
                row |= {'status': 'error', 'reason': 'result identity mismatch'}
            elif name in args.declared_declines:
                row['status'] = 'declared_decline' if result.get('exit_code') == 2 else 'error'
            elif result.get('exit_code') == 2:
                row['status'] = 'declined'
            elif result.get('exit_code') not in [0, 1] or not source or not source.exists():
                row |= {'status': 'error', 'reason': 'checker error or missing built input'}
            else:
                start = time.monotonic()
                try:
                    p = subprocess.run([str(reference), '--import', str(source)], capture_output=True, timeout=args.timeout)
                    row['reference'] = {'exit_code': p.returncode, 'seconds': round(time.monotonic() - start, 6),
                                        'stderr': p.stderr.decode(errors='replace')[-4000:]}
                    row['status'] = ('error' if p.returncode not in [0, 1]
                                     else 'match' if p.returncode == result['exit_code'] else 'mismatch')
                except subprocess.TimeoutExpired:
                    row |= {'status': 'error', 'reason': 'reference timeout'}
        counts[row['status']] += 1
        rows.append(row)
        if row['status'] in ['error', 'mismatch']:
            print(json.dumps(row), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({'reference_revision': revision, 'excluded_tests': excluded, 'summary': dict(counts), 'results': rows}, indent=2) + '\n')
    print(json.dumps(dict(counts), sort_keys=True))
    return int(bool(counts['error'] or counts['mismatch']))


if __name__ == '__main__':
    raise SystemExit(main())
