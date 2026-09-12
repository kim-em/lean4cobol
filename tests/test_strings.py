"""Unicode expansion, projections/recursors, and implicit replay dependencies."""
import copy
import hashlib
import json
from pathlib import Path
from test_kernel import Stream

FIXTURES = Path(__file__).parent / 'fixtures/strings'
DECLS = {'def', 'thm', 'axiom', 'opaque', 'inductive', 'quot'}


def encode(records):
    return '\n'.join(json.dumps(r, ensure_ascii=False) for r in records) + '\n'


def cases():
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    data = (FIXTURES / 'strings.ndjson').read_bytes()
    assert hashlib.sha256(data).hexdigest() == manifest['sha256']
    assert hashlib.sha256((Path(__file__).parent / 'strings.lean').read_bytes()).hexdigest() == manifest['source_sha256']
    base = [json.loads(line) for line in data.splitlines()]
    yield 'strings_reference', base, 0
    names = {0: ''}
    for r in base:
        if 'in' in r:
            v = r.get('str', r.get('num'))
            names[r['in']] = (names[v['pre']] + '.' if v['pre'] else '') + str(v.get('str', v.get('i')))
    es = {r['ie']: r for r in base if 'ie' in r}
    # Change only the expected side, leaving the proof and all shared input
    # nodes intact. Projection and recursor mutations retain their types.
    for target in [r['thm'] for r in base if names.get(r.get('thm', {}).get('name'), '').startswith('string')]:
        records = copy.deepcopy(base)
        d = next(r['thm'] for r in records if r.get('thm', {}).get('name') == target['name'])
        name = names[d['name']]
        root = es[d['type']]['app']
        eid = max(es) + 1
        additions = []
        if name.startswith('stringRecursor'):
            additions.append({'ie': eid, 'natVal': '38'})
        else:
            additions.append({'ie': eid, 'strVal': 'wrong'})
        rhs = eid
        if name == 'stringProjection':
            eid += 1
            additions.append({'ie': eid, 'app': {'fn': es[root['arg']]['app']['fn'], 'arg': rhs}})
            rhs = eid
        eid += 1
        additions.append({'ie': eid, 'app': {'fn': root['fn'], 'arg': rhs}})
        d['type'] = eid
        pos = records.index({'thm': d})
        records[pos:pos] = additions
        yield name + '_wrong_value', records, 1
    # Move a literal-bearing declaration before its implicit primitive
    # dependencies; scalar/table records remain topological for the parser.
    for first in ['stringLiteralOnly', 'stringLiteralBinder', 'stringTypeOnly']:
        records = copy.deepcopy(base)
        declarations = [r for r in records if DECLS.intersection(r)]
        records = [r for r in records if not DECLS.intersection(r)]
        target = next(r for r in declarations if any(names.get(v.get('name')) == first for v in r.values()))
        declarations.remove(target)
        records += [target, *declarations]
        yield first + '_forward_dependencies', records, 0
    for missing in ['String.ofList', 'Char.ofNat']:
        records = [r for r in base if names.get(r.get('def', {}).get('name')) != missing]
        yield 'missing_' + missing, records, 1
    # UTF-8 values must survive raw JSON and surrogate-pair JSON encodings.
    records = copy.deepcopy(base)
    encoded = '\n'.join(json.dumps(r, ensure_ascii=True) for r in records)
    yield 'escaped_unicode', [json.loads(line) for line in encoded.splitlines()], 0
    s = Stream()
    ty = s.const('String')
    value = s.expr('strVal', 'skipped 😀')
    s.definition('unsafeLiteral', ty, value)
    next(r['def'] for r in s.records if 'def' in r)['safety'] = 'unsafe'
    yield 'unsafe_literal_without_primitives', s.records, 0


def run(check):
    count = 0
    for name, records, expected in cases():
        try:
            # The escaped variant deliberately exercises JSON surrogate pairs.
            text = ('\n'.join(json.dumps(r, ensure_ascii=True) for r in records) + '\n'
                    if name == 'escaped_unicode' else encode(records))
            check(text, expected)
        except AssertionError as exc:
            raise AssertionError(name) from exc
        count += 1
    print(f'{count} string expansion and dependency regressions passed')


if __name__ == '__main__':
    dest = Path('tests/generated/strings')
    dest.mkdir(parents=True, exist_ok=True)
    for old in dest.glob('*.ndjson'):
        old.unlink()
    for name, records, expected in cases():
        text = ('\n'.join(json.dumps(r, ensure_ascii=True) for r in records) + '\n'
                if name == 'escaped_unicode' else encode(records))
        (dest / (name + '.ndjson')).write_text(text)
