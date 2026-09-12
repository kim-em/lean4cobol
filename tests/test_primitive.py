"""Primitive defining equations, independently checked by the pinned oracle."""
import copy
import hashlib
import json
from pathlib import Path

FIXTURES = Path(__file__).parent / 'fixtures/primitive'


def encode(records):
    return '\n'.join(json.dumps(r) for r in records) + '\n'


def basic_cases():
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    data = (FIXTURES / 'basics.ndjson').read_bytes()
    assert hashlib.sha256(data).hexdigest() == manifest['sha256']
    base = [json.loads(line) for line in data.splitlines()]
    yield 'reference_basics', base, 0
    names = {0: ''}
    for r in base:
        if 'in' in r:
            n = r.get('str', r.get('num'))
            pre = names[n['pre']]
            names[r['in']] = (pre + '.' if pre else '') + str(n.get('str', n.get('i')))
    name_ids = {v: k for k, v in names.items()}
    # Recursor binders consume only the four recognized type annotation
    # gadgets. Ordinary identity definitions must retain their syntax.
    for annotation in ['semiOutParam', 'optParam', 'autoParam', 'ordinaryIdentity']:
        records = copy.deepcopy(base)
        annotation_id = name_ids['outParam']
        for r in records:
            if r.get('in') == annotation_id:
                r['str']['str'] = annotation
        if annotation in ['optParam', 'autoParam']:
            old_exprs = {r['ie']: r for r in records if 'ie' in r}
            d = next(r['def'] for r in records if r.get('def', {}).get('name') == annotation_id)
            nat = next(i for i, r in old_exprs.items() if r.get('const', {}).get('name') == name_ids['Nat'])
            zero = next(i for i, r in old_exprs.items() if r.get('const', {}).get('name') == name_ids['Nat.zero'])
            annotation_consts = {i for i, r in old_exprs.items() if r.get('const', {}).get('name') == annotation_id}
            additions = []
            next_id = max(old_exprs) + 1

            def fresh(kind, value):
                nonlocal next_id
                eid = next_id
                next_id += 1
                additions.append({'ie': eid, kind: value})
                return eid

            ty = copy.deepcopy(old_exprs[d['type']]['forallE'])
            val = copy.deepcopy(old_exprs[d['value']]['lam'])
            ty['body'] = fresh('forallE', dict(ty, type=nat))
            val['body'] = fresh('lam', dict(val, type=nat, body=fresh('bvar', 1)))
            d['type'] = fresh('forallE', ty)
            d['value'] = fresh('lam', val)
            where = records.index({'def': d})
            records[where:where] = additions
            rewritten = []
            for r in records:
                if r.get('app', {}).get('fn') in annotation_consts:
                    inner = next_id
                    next_id += 1
                    rewritten.append({'ie': inner, 'app': copy.deepcopy(r['app'])})
                    r['app'] = {'fn': inner, 'arg': zero}
                rewritten.append(r)
            records = rewritten
        yield f'annotation_{annotation}', records, 1 if annotation == 'ordinaryIdentity' else 0

    targets = ['Nat.add', 'Nat.pred', 'Nat.sub', 'Nat.mul', 'Nat.pow', 'Nat.beq', 'Nat.ble', 'Nat.shiftLeft']
    for target in targets:
        for mutation in ['wrong_body', 'extra_universe', 'alias_body']:
            records = copy.deepcopy(base)
            d = next(r['def'] for r in records if names.get(r.get('def', {}).get('name')) == target)
            insertion = records.index({'def': d})
            additions = []
            next_expr = max(r['ie'] for r in records if 'ie' in r) + 1

            def expr(kind, value):
                nonlocal next_expr
                eid = next_expr
                next_expr += 1
                additions.append({'ie': eid, kind: value})
                return eid

            def const(name):
                return expr('const', {'name': name_ids[name], 'us': []})

            def lam(ty, body):
                return expr('lam', {'name': 0, 'type': ty, 'body': body, 'binderInfo': 'default'})

            if mutation == 'wrong_body':
                # These bodies have exactly the declared type. Ordinary type
                # checking would accept them, but their defining equations fail.
                nat = const('Nat')
                if target == 'Nat.pred':
                    body = lam(nat, const('Nat.zero'))
                elif target in ['Nat.beq', 'Nat.ble']:
                    body = lam(nat, lam(nat, const('Bool.true')))
                else:
                    body = lam(nat, lam(nat, expr('bvar', 1)))
                d['value'] = body
                expected = 1
            elif mutation == 'extra_universe':
                d['levelParams'] = [name_ids['Nat']]
                expected = 1
            else:
                # Shape validation uses definitional equality, and must accept
                # an extra delta step in the candidate body.
                nid = max(names) + 1
                additions.append({'in': nid, 'str': {'pre': 0, 'str': 'primitiveAlias'}})
                additions.append({'def': dict(d, name=nid, all=[nid], hints='abbrev')})
                d['value'] = expr('const', {'name': nid, 'us': []})
                expected = 0
            records[insertion:insertion] = additions
            yield f'{target}_{mutation}', records, expected


def division_cases():
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    data = (FIXTURES / 'division.ndjson').read_bytes()
    assert hashlib.sha256(data).hexdigest() == manifest['division']['sha256']
    base = [json.loads(line) for line in data.splitlines()]
    yield 'reference_division', base, 0
    names = {0: ''}
    for r in base:
        if 'in' in r:
            n = r.get('str', r.get('num'))
            pre = names[n['pre']]
            names[r['in']] = (pre + '.' if pre else '') + str(n.get('str', n.get('i')))
    name_ids = {v: k for k, v in names.items()}
    for target in ['Nat.mod', 'Nat.div']:
        for mutation in ['wrong_body', 'extra_universe', 'alias_body']:
            records = copy.deepcopy(base)
            d = next(r['def'] for r in records if names.get(r.get('def', {}).get('name')) == target)
            insertion = records.index({'def': d})
            eid = max(r['ie'] for r in records if 'ie' in r) + 1
            additions = []
            if mutation == 'wrong_body':
                nat = next(r['ie'] for r in records if r.get('const', {}).get('name') == name_ids['Nat'])
                # A correctly typed constant-zero body passes the mod-zero
                # equation; the successor/fuel equations must still reject it.
                zero = next(r['ie'] for r in records if r.get('const', {}).get('name') == name_ids['Nat.zero'])
                binder = lambda body: dict(name=0, type=nat, body=body, binderInfo='default')
                additions = [{'ie': eid, 'lam': binder(zero)}, {'ie': eid + 1, 'lam': binder(eid)}]
                d['value'] = eid + 1
                expected = 1
            elif mutation == 'extra_universe':
                d['levelParams'] = [name_ids['Nat']]
                expected = 1
            else:
                nid = max(names) + 1
                additions = [{'in': nid, 'str': {'pre': 0, 'str': 'primitiveAlias'}},
                             {'def': dict(d, name=nid, all=[nid], hints='abbrev')},
                             {'ie': eid, 'const': {'name': nid, 'us': []}}]
                d['value'] = eid
                expected = 0
            records[insertion:insertion] = additions
            yield f'{target}_{mutation}', records, expected

    # Same type does not certify a decider, conditional, or recursive helper.
    # Replace the implementation with an axiom at precisely the same type.
    for target in ['Nat.decLe', 'ite', 'dite', 'Nat.modCore.go', 'Nat.div.go']:
        records = copy.deepcopy(base)
        d = next(r['def'] for r in records if names.get(r.get('def', {}).get('name')) == target)
        insertion = records.index({'def': d})
        nid = max(names) + 1
        eid = max(r['ie'] for r in records if 'ie' in r) + 1
        us = [next(r['il'] for r in records if r.get('param') == p) for p in d['levelParams']]
        additions = [{'in': nid, 'str': {'pre': 0, 'str': 'counterfeitImplementation'}},
                     {'axiom': dict(name=nid, levelParams=d['levelParams'], type=d['type'], isUnsafe=False)},
                     {'ie': eid, 'const': {'name': nid, 'us': us}}]
        d['value'] = eid
        records[insertion:insertion] = additions
        yield f'counterfeit_{target}', records, 1

    # Reflection proofs may be axioms: the reference checks their proposition
    # and uses proof irrelevance, without requiring a specific proof body.
    for target in ['Nat.le_of_ble_eq_true', 'Nat.not_le_of_not_ble_eq_true']:
        records = copy.deepcopy(base)
        r = next(r for r in records if names.get(r.get('thm', {}).get('name')) == target)
        d = r.pop('thm')
        r['axiom'] = dict(name=d['name'], levelParams=d['levelParams'], type=d['type'], isUnsafe=False)
        yield f'axiom_reflection_proof_{target}', records, 0


def cases():
    yield from basic_cases()
    yield from division_cases()


def run(check):
    count = 0
    for name, records, expected in cases():
        try:
            check(encode(records), expected)
        except AssertionError as exc:
            raise AssertionError(name) from exc
        count += 1
    print(f'{count} primitive definition regressions passed')


if __name__ == '__main__':
    root = Path('tests/generated/primitive')
    root.mkdir(parents=True, exist_ok=True)
    for old in root.glob('*.ndjson'):
        old.unlink()
    for i, (name, records, expected) in enumerate(cases()):
        (root / f'{i:03}_{expected}_{name}.ndjson').write_text(encode(records))
