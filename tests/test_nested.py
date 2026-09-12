"""Nested lowering/restoration, recursor regeneration, and malformed inputs."""
import copy
import hashlib
import json
from pathlib import Path

FIXTURES = Path(__file__).parent / 'fixtures/nested'


def encode(records):
    return '\n'.join(json.dumps(r) for r in records) + '\n'


def cases():
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    data = (FIXTURES / 'nested.ndjson').read_bytes()
    assert hashlib.sha256(data).hexdigest() == manifest['sha256']
    assert hashlib.sha256((Path(__file__).parent / 'nested.lean').read_bytes()).hexdigest() == manifest['source_sha256']
    base = [json.loads(line) for line in data.splitlines()]
    names = {0: ''}
    for r in base:
        if 'in' in r:
            n = r.get('str', r.get('num'))
            pre = names[n['pre']]
            names[r['in']] = (pre + '.' if pre else '') + str(n.get('str', n.get('i')))
    ids = {v: k for k, v in names.items()}
    yield 'reference_nested', base, 0
    for count in [0, 500]:
        records = copy.deepcopy(base)
        for r in records:
            for d in r.get('inductive', {}).get('types', []):
                d['numNested'] = count
        yield f'ignored_numNested_{count}', records, 0

    for mutation in ['missing_export', 'rule_ctor', 'rule_fields', 'params', 'collision']:
        records = copy.deepcopy(base)
        r = next(r for r in records if any(names[t['name']] == 'NestedRose' for t in r.get('inductive', {}).get('types', [])))
        pkg = r['inductive']
        rec = next(d for d in pkg['recs'] if names[d['name']] == 'NestedRose.rec_1')
        expected = 1
        if mutation in ['missing_export', 'collision']:
            pkg['recs'].remove(rec)
            if mutation == 'missing_export':
                expected = 0
            else:
                eid = max(e['ie'] for e in records if 'ie' in e) + 1
                pos = records.index(r)
                records[pos:pos] = [{'ie': eid, 'sort': 0}, {'axiom': dict(name=rec['name'], levelParams=[], type=eid, isUnsafe=False)}]
        elif mutation == 'rule_ctor':
            rec['rules'][0]['ctor'] = ids['NestedRose.node']
        elif mutation == 'rule_fields':
            rec['rules'][0]['nfields'] += 1
        else:
            rec['numParams'] += 1
        yield f'nested_aux_{mutation}', records, expected

    # The recursive occurrence lies in List's parameter, but its index refers
    # to a constructor-local binder. The reference explicitly forbids this.
    records = copy.deepcopy(base)
    pkg_record = next(r for r in records if any(names[t['name']] == 'NestedIndexed' for t in r.get('inductive', {}).get('types', [])))
    ctor = pkg_record['inductive']['ctors'][0]
    exprs = {r['ie']: r for r in records if 'ie' in r}
    outer = exprs[ctor['type']]['forallE']
    inner = exprs[outer['body']]['forallE']
    list_app = exprs[inner['type']]['app']
    ind_app = exprs[list_app['arg']]['app']
    ind_const = exprs[ind_app['fn']]['app']['fn']
    result_index = exprs[inner['body']]['app']['arg']
    nat = next(i for i, r in exprs.items() if r.get('const', {}).get('name') == ids['Nat'])
    eid = max(exprs) + 1
    additions = []

    def fresh(kind, value):
        nonlocal eid
        result = eid
        eid += 1
        additions.append({'ie': result, kind: value})
        return result

    def app(fn, arg):
        return fresh('app', dict(fn=fn, arg=arg))

    def pi(ty, body):
        return fresh('forallE', dict(name=0, type=ty, body=body, binderInfo='default'))

    b0, b1, b2 = (fresh('bvar', i) for i in range(3))
    field = app(list_app['fn'], app(app(ind_const, b1), b0))
    result = app(app(ind_const, b2), result_index)
    ctor['type'] = pi(outer['type'], pi(nat, pi(field, result)))
    pos = records.index(pkg_record)
    records[pos:pos] = additions
    yield 'nested_local_index_forbidden', records, 1

    # Auxiliary names use Name.appendIndexAfter, including hygienic scopes and
    # names whose final component is numeric. Renaming the existing container
    # exercises that operation inside the lowering/restoration path.
    for variant in ['numeric', 'scoped', 'empty_scopes']:
        records = copy.deepcopy(base)
        nid = max(names) + 1
        target = ids['NestContainerTree']
        original = next(r for r in records if r.get('in') == target)
        pos = records.index(original)
        extra = [{'in': nid, 'str': copy.deepcopy(original['str'])}]
        pre = nid
        if variant != 'numeric':
            for part in ['_@', 'Fixture', '_hyg']:
                nid += 1
                extra.append({'in': nid, 'str': {'pre': pre, 'str': part}})
                pre = nid
        original.clear()
        if variant == 'empty_scopes':
            last = extra.pop()
            original.update({'in': target, 'str': last['str']})
        else:
            original.update({'in': target, 'num': {'pre': pre, 'i': 17}})
        records[pos:pos] = extra
        yield f'nested_name_{variant}', records, 0


def run(check):
    count = 0
    for name, records, expected in cases():
        try:
            check(encode(records), expected)
        except AssertionError as exc:
            raise AssertionError(name) from exc
        count += 1
    print(f'{count} nested inductive regressions passed')


if __name__ == '__main__':
    root = Path('tests/generated/nested')
    root.mkdir(parents=True, exist_ok=True)
    for old in root.glob('*.ndjson'):
        old.unlink()
    for i, (name, records, expected) in enumerate(cases()):
        (root / f'{i:03}_{expected}_{name}.ndjson').write_text(encode(records))
