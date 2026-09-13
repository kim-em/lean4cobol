#!/usr/bin/env python3
"""Prepare a pinned upstream arena entry and patch, without publishing either."""
import argparse
import json
import re
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def duration(seconds):
    hours, rest = divmod(round(seconds), 3600)
    minutes, seconds = divmod(rest, 60)
    return f'{hours} h {minutes} m {seconds} s'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--revision', required=True, help='Source commit containing the validated implementation')
    parser.add_argument('--ref', default='main')
    parser.add_argument('--output', type=Path, default=ROOT / '_tmp/arena-submission')
    args = parser.parse_args()
    revision = subprocess.check_output(['git', 'rev-parse', '--verify', args.revision + '^{commit}'], cwd=ROOT, text=True).strip()
    url = subprocess.check_output(['git', 'remote', 'get-url', 'origin'], cwd=ROOT, text=True).strip()
    if url.startswith('git@github.com:'):
        url = 'https://github.com/' + url.removeprefix('git@github.com:')
    config = subprocess.check_output(['git', 'show', revision + ':arena/lean4cobol.yaml'], cwd=ROOT, text=True)
    results = json.loads(subprocess.check_output(
        ['git', 'show', revision + ':docs/results.json'], cwd=ROOT, text=True))
    benchmarks = json.loads(subprocess.check_output(
        ['git', 'show', revision + ':docs/benchmarks.json'], cwd=ROOT, text=True))
    assert config.count('dir: ..\n') == 1
    config = config.replace('dir: ..\n', f'url: {json.dumps(url)}\nref: {json.dumps(args.ref)}\nrev: {revision}\n')
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'lean4cobol.yaml').write_text(config)
    lines = config.splitlines()
    patch = ('diff --git a/checkers/lean4cobol.yaml b/checkers/lean4cobol.yaml\n'
             'new file mode 100644\n--- /dev/null\n+++ b/checkers/lean4cobol.yaml\n'
             f'@@ -0,0 +1,{len(lines)} @@\n' + ''.join('+' + line + '\n' for line in lines))
    (args.output / 'lean4cobol.patch').write_text(patch)
    mathlib = {run['checker']: run for run in benchmarks['runs'] if run['suite'] == 'mathlib'}
    checker, reference = mathlib['lean4cobol'], mathlib['lean4lean']
    measured = results['summary'].get('match', 0)
    unmeasured = [row['test'] for row in results['results'] if row['status'] == 'not_run']
    report_url = url.removesuffix('.git') + f'/blob/{revision}/docs/performance.md'
    declines = re.search(r'^declines:\n((?:[ \t]+-[^\n]*\n)+)', config, re.M)
    decline_note = ('The arena entry declines ' + ', '.join(
        line.strip().removeprefix('-').strip() for line in declines[1].splitlines())
        + ' for benchmark cost; direct checking remains supported.'
        if declines else 'No libraries are predeclared as declined.')
    body = (
        'Add lean4cobol, a GnuCOBOL port of lean4lean’s executable kernel, pinned to '
        f'`{revision}`. The Nix build environment is pinned and the launcher has '
        f'no wall-clock timeout. {decline_note}\n\n'
        f'Validation: {measured} measured inputs agree with the pinned lean4lean '
        'reference. Release and checked regression suites pass. The checker uses '
        'exit codes 0/1/2 for acceptance/rejection/resource decline.\n\n'
        f'Mathlib accepts in {duration(checker["seconds"])} with '
        f'{checker["max_rss_bytes"] / 1024**3:.2f} GiB peak RSS, versus '
        f'{duration(reference["seconds"])} for lean4lean. These are shared-host '
        f'measurements; see the [results and methodology]({report_url}).\n')
    if unmeasured:
        body += '\nNo completed measurement is recorded for: ' + ', '.join(unmeasured) + '.\n'
    (args.output / 'pr-body.md').write_text(body)
    print(args.output)


if __name__ == '__main__':
    main()
