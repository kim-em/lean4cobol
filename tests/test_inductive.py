"""Inductive/quotient fixture, metadata-tampering, and parser regressions."""
import copy
import hashlib
import json
from pathlib import Path

from test_kernel import Stream

FIXTURES = Path(__file__).parent / 'fixtures/inductive'


def encode(records):
    return '\n'.join(json.dumps(r) for r in records) + '\n'


def cases():
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    bases = {}
    for row in manifest['files']:
        data = (FIXTURES / row['file']).read_bytes()
        assert hashlib.sha256(data).hexdigest() == row['sha256'], row['file']
        records = [json.loads(line) for line in data.splitlines()]
        bases[int(row['file'][:3])] = records
        yield row['file'], records, row['expected']

    mutual_dir = FIXTURES.parent / 'mutual'
    mutual_manifest = json.loads((mutual_dir / 'manifest.json').read_text())
    mutual_data = (mutual_dir / 'mutual.ndjson').read_bytes()
    assert hashlib.sha256(mutual_data).hexdigest() == mutual_manifest['sha256']
    source = Path(__file__).parent / 'mutual.lean'
    assert hashlib.sha256(source.read_bytes()).hexdigest() == mutual_manifest['source_sha256']
    mutual = [json.loads(line) for line in mutual_data.splitlines()]
    yield 'mutual_parameterized_indexed_reduction', mutual, 0
    for package in range(2):
        for mutation in ['all', 'rule_fields']:
            records = copy.deepcopy(mutual)
            blocks = [r['inductive'] for r in records if len(r.get('inductive', {}).get('types', [])) > 1]
            rec = blocks[package]['recs'][0]
            if mutation == 'all':
                rec['all'].reverse()
            else:
                rec['rules'][0]['nfields'] += 1
            yield f'mutual_{package}_{mutation}', records, 1

    # Nat literals are arbitrary decimal byte strings. Exercise a carry chain
    # far beyond machine integers, and a near miss that must reject.
    samples = [('zero', '0', None, 0), ('one', '1', '0', 0),
               ('borrow', '10', '9', 0), ('large', '1' + '0' * 120, '9' * 120, 0),
               ('huge', '1' + '0' * 5000, '9' * 5000, 0), ('wrong', '1000', '998', 1)]
    for label, literal, pred, expected in samples:
        records = copy.deepcopy(bases[103])
        names = {0: ''}
        for r in records:
            if 'in' in r:
                node = r.get('str', r.get('num'))
                prefix = names[node['pre']]
                part = str(node.get('str', node.get('i')))
                names[r['in']] = prefix + '.' + part if prefix else part
        succ_name = next(n for n, text in names.items() if text == 'Nat.succ')
        zero_name = next(n for n, text in names.items() if text == 'Nat.zero')
        succ = next(r['ie'] for r in records if r.get('const', {}).get('name') == succ_name)
        zero = next(r['ie'] for r in records if r.get('const', {}).get('name') == zero_name)
        for r in records:
            if 'natVal' in r:
                r['natVal'] = literal
        thm = records[-1]['thm']
        ty = next(r for r in records if r.get('ie') == thm['type'])
        if pred is None:
            ty['app']['arg'] = zero
        else:
            eid = max(r['ie'] for r in records if 'ie' in r) + 1
            ty['app']['arg'] = eid + 1
            # Definitions of new expression IDs precede the type that uses them.
            where = records.index(ty)
            records[where:where] = [{'ie': eid, 'natVal': pred},
                                   {'ie': eid + 1, 'app': {'fn': succ, 'arg': eid}}]
        yield f'nat_literal_{label}', records, expected

    # Generated metadata, not exported flags, determines inductive semantics.
    for n in (36, 43, 44):
        for field, value in [('isRec', False), ('isRec', True), ('isReflexive', True),
                             ('numIndices', 400), ('numNested', 500)]:
            records = copy.deepcopy(bases[n])
            pkg = next(r['inductive'] for r in records if 'inductive' in r)
            pkg['types'][0][field] = value
            yield f'ignored_inductive_{n}_{field}_{value}', records, 0

    # Constructor and recursor records, in contrast, are compared exactly with
    # regenerated declarations at the end of replay.
    for family, fields in [('ctors', ['cidx', 'numParams', 'numFields']),
                           ('recs', ['numParams', 'numIndices', 'numMotives', 'numMinors'])]:
        for field in fields:
            records = copy.deepcopy(bases[44])
            pkg = next(r['inductive'] for r in records if 'inductive' in r)
            pkg[family][0][field] += 1
            yield f'bad_{family}_{field}', records, 1
    for mutation in ('k', 'missing_rule', 'extra_rule', 'rule_fields', 'rule_rhs', 'all'):
        records = copy.deepcopy(bases[44])
        pkg = next(r['inductive'] for r in records if 'inductive' in r)
        rec = pkg['recs'][0]
        if mutation == 'k':
            rec['k'] = not rec['k']
        elif mutation == 'missing_rule':
            rec['rules'].pop()
        elif mutation == 'extra_rule':
            rec['rules'].append(copy.deepcopy(rec['rules'][0]))
        elif mutation == 'rule_fields':
            rec['rules'][0]['nfields'] += 1
        elif mutation == 'rule_rhs':
            rec['rules'][0]['rhs'] = rec['type']
        else:
            rec['all'] = []
        yield f'bad_rec_{mutation}', records, 1

    for family, field in [('types', 'ctors'), ('types', 'numNested'), ('types', 'isRec'),
                          ('ctors', 'induct'), ('ctors', 'numFields'), ('recs', 'rules'),
                          ('recs', 'k'), ('recs', 'numMotives')]:
        records = copy.deepcopy(bases[44])
        pkg = next(r['inductive'] for r in records if 'inductive' in r)
        del pkg[family][0][field]
        yield f'missing_{family}_{field}', records, 1

    for family in ('ctors', 'recs'):
        s = Stream()
        ty = s.sort()
        name = s.name('orphan')
        pkg = {'types': [], 'ctors': [], 'recs': []}
        if family == 'ctors':
            pkg['ctors'] = [dict(name=name, levelParams=[], type=ty, induct=name,
                                cidx=0, numParams=0, numFields=0, isUnsafe=False)]
        else:
            pkg['recs'] = [dict(name=name, levelParams=[], type=ty, all=[], numParams=0,
                               numIndices=0, numMotives=0, numMinors=0, rules=[], k=False, isUnsafe=False)]
        s.records.append({'inductive': pkg})
        yield f'orphan_{family}', s.records, 1

    # Primitive names cannot be introduced as arbitrary axioms, including when
    # they are otherwise unused. A malformed primitive inductive also rejects.
    for name in ['Nat', 'Bool', 'Nat.add', 'String.ofList', 'Char.ofNat']:
        s = Stream()
        s.axiom(name, s.sort())
        yield f'primitive_axiom_{name}', s.records, 1
    records = copy.deepcopy(bases[44])
    pkg = next(r['inductive'] for r in records if 'inductive' in r)
    pkg['types'][0]['ctors'].reverse()
    yield 'primitive_ctor_order', records, 1

    s = Stream()
    universe = s.sort(s.level('succ', 0))
    A = s.axiom('_nested.A', universe)
    T = s.const('T')
    ctor_ty = s.pi(A, T)
    t_name, ctor_name = s.name('T'), s.name('T.mk')
    s.records.append({'inductive': {
        'types': [dict(name=t_name, levelParams=[], type=universe, all=[t_name], ctors=[ctor_name],
                       numParams=0, numIndices=0, numNested=0, isRec=False, isReflexive=False, isUnsafe=False)],
        'ctors': [dict(name=ctor_name, levelParams=[], type=ctor_ty, induct=t_name, cidx=0,
                       numParams=0, numFields=1, isUnsafe=False)], 'recs': []}})
    yield 'reserved_nested_prefix', s.records, 1

    # Quot.mk/lift/ind exports are erased by the reference importer; the
    # generated declarations must supply their types and reductions.
    records = copy.deepcopy(bases[131])
    for r in records:
        if 'quot' in r and r['quot']['kind'] != 'type':
            r['quot']['type'] = 0
            r['quot']['levelParams'] = []
    yield 'ignored_quotient_headers', records, 0


def run(check):
    count = 0
    for name, records, expected in cases():
        try:
            check(encode(records), expected)
        except AssertionError as exc:
            raise AssertionError(name) from exc
        count += 1
    print(f'{count} inductive, recursor, quotient, and metadata regressions passed')


if __name__ == '__main__':
    root = Path('tests/generated/inductive')
    root.mkdir(parents=True, exist_ok=True)
    for old in root.glob('*.ndjson'):
        old.unlink()
    for i, (name, records, expected) in enumerate(cases()):
        safe = ''.join(c if c.isalnum() or c == '_' else '-' for c in name)
        (root / f'{i:03}_{expected}_{safe}.ndjson').write_text(encode(records))
