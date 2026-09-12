"""Well-founded primitive validation, including well-typed counterfeit bodies."""
import copy
import hashlib
import json
from pathlib import Path

FIXTURES = Path(__file__).parent / 'fixtures/primitive'


def encode(records):
    return '\n'.join(json.dumps(r) for r in records) + '\n'


def cases():
    data = (FIXTURES / 'well-founded.ndjson').read_bytes()
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())['well_founded']
    assert hashlib.sha256(data).hexdigest() == manifest['sha256']
    assert hashlib.sha256((Path(__file__).parent / 'well-founded.lean').read_bytes()).hexdigest() == manifest['source_sha256']
    base = [json.loads(line) for line in data.splitlines()]
    yield 'well_founded_reference', base, 0
    names = {0: ''}
    for r in base:
        if 'in' in r:
            v = r.get('str', r.get('num'))
            names[r['in']] = (names[v['pre']] + '.' if v['pre'] else '') + str(v.get('str', v.get('i')))
    nids = {v: k for k, v in names.items()}
    es = {r['ie']: r for r in base if 'ie' in r}
    nat = next(i for i, r in es.items() if r.get('const') == {'name': nids['Nat'], 'us': []})
    zero = next(i for i, r in es.items() if r.get('const') == {'name': nids['Nat.zero'], 'us': []})
    succ = next(i for i, r in es.items() if r.get('const') == {'name': nids['Nat.succ'], 'us': []})

    def declaration(records, name):
        return next(r['def'] for r in records if r.get('def', {}).get('name') == nids[name])

    def rename_primitives(records):
        for r in records:
            if names.get(r.get('in')) in ['Nat.gcd', 'Nat.bitwise', 'Nat.land', 'Nat.lor', 'Nat.xor']:
                r['str']['str'] = 'custom_' + r['str']['str']

    def ordinary_control(records):
        control = copy.deepcopy(records)
        # Remove the arithmetic assertions: the forged definitions deliberately
        # compute different values. The control checks their types and helpers.
        control = [r for r in control if not names.get(r.get('thm', {}).get('name'), '').startswith('wfArithmetic')]
        rename_primitives(control)
        return control

    for target in [r['thm'] for r in base if names.get(r.get('thm', {}).get('name'), '').startswith('wfArithmetic')]:
        records = copy.deepcopy(base)
        d = next(r['thm'] for r in records if r.get('thm', {}).get('name') == target['name'])
        eid = max(es) + 1
        expr = {'ie': eid, 'app': dict(es[d['type']]['app'], arg=zero)}
        d['type'] = eid
        records.insert(records.index({'thm': d}), expr)
        yield names[d['name']] + '_wrong_result', records, 1

    targets = ['Nat.gcd', 'Nat.bitwise', 'Nat.land', 'Nat.lor', 'Nat.xor']
    for name in targets:
        for mutation in ['zero_body', 'extra_universe', 'zeta_body']:
            records = copy.deepcopy(base)
            d = declaration(records, name)
            additions = []
            eid = max(es) + 1

            def fresh(kind, value):
                nonlocal eid
                result = eid
                eid += 1
                additions.append({'ie': result, kind: value})
                return result

            if mutation == 'extra_universe':
                d['levelParams'] = [nids['Nat']]
            elif mutation == 'zeta_body':
                d['value'] = fresh('letE', {'name': 0, 'type': d['type'], 'value': d['value'],
                                          'body': fresh('bvar', 0), 'nondep': False})
            else:
                body = zero
                for _ in range(2):
                    body = fresh('lam', {'name': 0, 'type': nat, 'body': body, 'binderInfo': 'default'})
                if name == 'Nat.bitwise':
                    function_ty = es[d['type']]['forallE']['type']
                    body = fresh('lam', {'name': 0, 'type': function_ty, 'body': body, 'binderInfo': 'default'})
                d['value'] = body
            pos = records.index({'def': d})
            records[pos:pos] = additions
            # land/lor/xor require a literal bitwise application at the head;
            # even a zeta-equivalent wrapper violates that structural check.
            expected = 0 if mutation == 'zeta_body' and name in ['Nat.gcd', 'Nat.bitwise'] else 1
            yield name + '_' + mutation, records, expected

    # Preserve the fix combinator and all functional parameter types, but
    # replace the recursive functional's result with zero. Ordinary checking
    # accepts these after renaming the primitive entry points; the primitive
    # equation validator must reject them.
    for name in ['Nat.gcd._unary', 'Nat.bitwise._unary']:
        records = copy.deepcopy(base)
        d = declaration(records, name)
        current = d['value']
        outer = []
        while 'lam' in es[current]:
            outer.append(es[current]['lam'])
            current = es[current]['lam']['body']
        assert 'app' in es[current]
        functional = es[current]['app']['arg']
        binders = []
        while 'lam' in es[functional]:
            binders.append(es[functional]['lam'])
            functional = es[functional]['lam']['body']
        assert len(binders) == 2
        additions = []
        eid = max(es) + 1

        def fresh(kind, value):
            nonlocal eid
            result = eid
            eid += 1
            additions.append({'ie': result, kind: value})
            return result

        body = zero
        for binder in reversed(binders):
            body = fresh('lam', dict(binder, body=body))
        body = fresh('app', dict(es[current]['app'], arg=body))
        for binder in reversed(outer):
            body = fresh('lam', dict(binder, body=body))
        d['value'] = body
        pos = records.index({'def': d})
        records[pos:pos] = additions
        yield name + '_wrong_functional', records, 1
        yield name + '_ordinary_control', ordinary_control(records), 0

    # Computationally harmless beta wrappers must still fail the exact
    # argument/fuel-independence checks in unfoldNatWellFounded.
    for capture_fuel in [False, True]:
        name = 'WellFounded.Nat.fix.go' if capture_fuel else 'WellFounded.Nat.fix'
        records = copy.deepcopy(base)
        d = declaration(records, name)
        outer = []
        current = d['value']
        while 'lam' in es[current]:
            outer.append(es[current]['lam'])
            current = es[current]['lam']['body']
        additions = []
        eid = max(es) + 1

        def fresh(kind, value):
            nonlocal eid
            result = eid
            eid += 1
            additions.append({'ie': result, kind: value})
            return result

        memo = {}
        def lift(old, depth=0):
            if (old, depth) in memo:
                return memo[old, depth]
            kind, value = next((k, v) for k, v in es[old].items() if k != 'ie')
            new = copy.deepcopy(value)
            if kind == 'bvar' and value >= depth:
                new = value + 1
            elif kind == 'app':
                new = {k: lift(v, depth) for k, v in value.items()}
            elif kind in ['lam', 'forallE']:
                new['type'] = lift(value['type'], depth)
                new['body'] = lift(value['body'], depth + 1)
            elif kind == 'letE':
                new['type'] = lift(value['type'], depth)
                new['value'] = lift(value['value'], depth)
                new['body'] = lift(value['body'], depth + 1)
            elif kind == 'proj':
                new['struct'] = lift(value['struct'], depth)
            elif kind == 'mdata':
                new = lift(value, depth)
            result = old if new == value else fresh(kind, new)
            memo[old, depth] = result
            return result

        if capture_fuel:
            function = es[current]['app']['fn']
            fuel = es[current]['app']['arg']
            wrapper = fresh('lam', {'name': 0, 'type': nat, 'body': lift(function), 'binderInfo': 'default'})
            function = fresh('app', {'fn': wrapper, 'arg': fuel})
            body = fresh('app', {'fn': function, 'arg': fuel})
        else:
            args = []
            head = current
            while 'app' in es[head]:
                args.insert(0, es[head]['app']['arg'])
                head = es[head]['app']['fn']
            assert len(args) == 7
            wrapper = fresh('lam', {'name': 0, 'type': nat, 'body': lift(args[3]), 'binderInfo': 'default'})
            args[3] = fresh('app', {'fn': wrapper, 'arg': zero})
            body = head
            for arg in args:
                body = fresh('app', {'fn': body, 'arg': arg})
        for binder in reversed(outer):
            body = fresh('lam', dict(binder, body=body))
        d['value'] = body
        pos = records.index({'def': d})
        records[pos:pos] = additions
        label = 'captured_fuel' if capture_fuel else 'wrapped_functional'
        yield label, records, 1
        yield label + '_ordinary_control', ordinary_control(records), 0

    for name in ['WellFounded.Nat.fix', 'WellFounded.Nat.fix.go']:
        records = copy.deepcopy(base)
        d = declaration(records, name)
        name_id = max(names) + 1
        eid = max(es) + 1
        additions = [{'in': name_id, 'str': {'pre': 0, 'str': 'counterfeitFix'}},
                     {'axiom': {'name': name_id, 'levelParams': d['levelParams'], 'type': d['type'], 'isUnsafe': False}}]
        # The alias carries exactly the original universe parameters.
        params = []
        next_level = max(r['il'] for r in records if 'il' in r) + 1
        for n in d['levelParams']:
            additions.append({'il': next_level, 'param': n})
            params.append(next_level)
            next_level += 1
        additions.append({'ie': eid, 'const': {'name': name_id, 'us': params}})
        d['value'] = eid
        pos = records.index({'def': d})
        records[pos:pos] = additions
        yield name + '_counterfeit', records, 1

    records = copy.deepcopy(base)
    d = declaration(records, 'WellFounded.Nat.eager')
    eid = max(es) + 1
    additions = [{'ie': eid, 'bvar': 0}, {'ie': eid + 1, 'app': {'fn': succ, 'arg': eid}},
                 {'ie': eid + 2, 'lam': {'name': 0, 'type': nat, 'body': eid + 1, 'binderInfo': 'default'}}]
    d['value'] = eid + 2
    pos = records.index({'def': d})
    records[pos:pos] = additions
    yield 'eager_wrong_fuel', records, 1


def run(check):
    count = 0
    for name, records, expected in cases():
        try:
            check(encode(records), expected)
        except AssertionError as exc:
            raise AssertionError(name) from exc
        count += 1
    print(f'{count} well-founded primitive regressions passed')


if __name__ == '__main__':
    dest = Path('tests/generated/well-founded')
    dest.mkdir(parents=True, exist_ok=True)
    for old in dest.glob('*.ndjson'):
        old.unlink()
    for name, records, expected in cases():
        (dest / (name + '.ndjson')).write_text(encode(records))
