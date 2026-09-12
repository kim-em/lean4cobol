"""Exported arithmetic equalities and forged results, checked against Lean."""
import copy
import hashlib
import json
from pathlib import Path
from test_kernel import Stream

FIXTURES = Path(__file__).parent / 'fixtures/arithmetic'


def cases():
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    data = (FIXTURES / 'arithmetic.ndjson').read_bytes()
    assert hashlib.sha256(data).hexdigest() == manifest['sha256']
    records = [json.loads(line) for line in data.splitlines()]
    yield 'arithmetic_reference', records, 0
    names = {0: ''}
    for r in records:
        if 'in' in r:
            v = r.get('str', r.get('num'))
            names[r['in']] = (names[v['pre']] + '.' if v['pre'] else '') + str(v.get('str', v.get('i')))
    es = {r['ie']: r for r in records if 'ie' in r}
    false = next(i for i, r in es.items() if names.get(r.get('const', {}).get('name')) == 'Bool.false')
    for target in [r['thm'] for r in records if names.get(r.get('thm', {}).get('name'), '').startswith('arithmetic')]:
        rs = copy.deepcopy(records)
        d = next(r['thm'] for r in rs if r.get('thm', {}).get('name') == target['name'])
        original = es[d['type']]['app']
        expected = es[original['arg']]
        next_id = max(es) + 1
        additions = []
        if 'natVal' in expected:
            additions.append({'ie': next_id, 'natVal': str(int(expected['natVal']) + 1)})
            wrong = next_id
            next_id += 1
        else:
            wrong = false
        additions.append({'ie': next_id, 'app': {'fn': original['fn'], 'arg': wrong}})
        d['type'] = next_id
        rs[rs.index({'thm': d}):rs.index({'thm': d})] = additions
        yield names[target['name']] + '_wrong_result', rs, 1
    # These names are ordinary declarations until the native host-code hook
    # sees exactly an application to a constant. Extra universes do not match.
    for hook in ['Lean.reduceNat', 'Lean.reduceBool', 'reduceNat', 'reduceBool']:
        for poly in [False, True]:
            s = Stream()
            A = s.axiom('A', s.sort(s.level('succ', 0)))
            c = s.axiom('c', A)
            fn = s.definition(hook, s.pi(A, A), s.lam(A, s.expr('bvar', 0)), params=['u'] if poly else [])
            if poly:
                fn = s.const(hook, [0])
            value = s.app(fn, c)
            F = s.axiom('F', s.pi(A, s.sort(s.level('succ', 0))))
            x = s.axiom('x', s.app(F, value))
            s.definition('check', s.app(F, c), x)
            yield f'{hook}_' + ('extra_universe' if poly else 'constant_argument'), s.records, int(not poly and hook.startswith('Lean.'))


def run(check):
    count = 0
    for name, records, verdict in cases():
        check('\n'.join(json.dumps(r) for r in records) + '\n', verdict)
        count += 1
    print(f'{count} arithmetic and native-hook kernel regressions passed')


if __name__ == '__main__':
    dest = Path('tests/generated/arithmetic')
    dest.mkdir(parents=True, exist_ok=True)
    for name, records, _ in cases():
        (dest / (name + '.ndjson')).write_text('\n'.join(json.dumps(r) for r in records) + '\n')
