"""Focused dependent-kernel cases, also exportable for the pinned oracle.

These cases use axioms to isolate equality rules without requiring inductives.
Run directly to materialize streams, or through test.py for local regressions.
"""
import json
from pathlib import Path

HEADER = {'meta': {'exporter': {'name': 'test', 'version': '1'},
                   'format': {'version': '3.1.0'},
                   'lean': {'version': '4.33.0-rc2', 'githash': '0' * 40}}}


class Stream:
    def __init__(self):
        self.records = [HEADER]
        self.names = {}
        self.exprs = {}
        self.levels = {}

    def name(self, name):
        if name not in self.names:
            prefix, _, part = name.rpartition('.')
            parent = self.name(prefix) if prefix else 0
            n = len(self.names) + 1
            self.names[name] = n
            self.records.append({'in': n, 'str': {'pre': parent, 'str': part}})
        return self.names[name]

    def expr(self, kind, value):
        key = json.dumps((kind, value), sort_keys=True)
        if key not in self.exprs:
            n = len(self.exprs)
            self.exprs[key] = n
            self.records.append({'ie': n, kind: value})
        return self.exprs[key]

    def level(self, kind, value):
        key = json.dumps((kind, value), sort_keys=True)
        if key not in self.levels:
            n = len(self.levels) + 1
            self.levels[key] = n
            self.records.append({'il': n, kind: value})
        return self.levels[key]

    def sort(self, level=0):
        return self.expr('sort', level)

    def app(self, fn, arg):
        return self.expr('app', {'fn': fn, 'arg': arg})

    def binder(self, kind, domain, body):
        return self.expr(kind, {'name': 0, 'type': domain, 'body': body, 'binderInfo': 'default'})

    def pi(self, domain, body):
        return self.binder('forallE', domain, body)

    def lam(self, domain, body):
        return self.binder('lam', domain, body)

    def const(self, name, us=()):
        return self.expr('const', {'name': self.name(name), 'us': list(us)})

    def axiom(self, name, ty, params=()):
        self.records.append({'axiom': {'name': self.name(name), 'levelParams': [self.name(p) for p in params],
                                       'type': ty, 'isUnsafe': False}})
        return self.const(name)

    def definition(self, name, ty, val, params=(), hints='abbrev', kind='def'):
        n = self.name(name)
        info = {'name': n, 'levelParams': [self.name(p) for p in params], 'type': ty, 'value': val, 'all': [n]}
        if kind == 'def':
            info |= {'safety': 'safe', 'hints': hints}
        elif kind == 'opaque':
            info |= {'isUnsafe': False}
        self.records.append({kind: info})
        return self.const(name)

    def text(self):
        return '\n'.join(json.dumps(r) for r in self.records) + '\n'


def cases():
    for prop in (False, True):
        for reverse in (False, True):
            s = Stream()
            universe = s.sort(s.level('succ', 0))
            A = s.axiom('A', s.sort() if prop else universe)
            a = s.axiom('a', A)
            b = s.axiom('b', A)
            F = s.axiom('F', s.pi(A, universe))
            fa, fb = s.app(F, a), s.app(F, b)
            if reverse:
                fa, fb = fb, fa
            x = s.axiom('x', fa)
            s.definition('test', fb, x)
            yield f'proof_irrel_{prop}_{reverse}', s, 0 if prop else 1

    for reverse in (False, True):
        for correct in (False, True):
            s = Stream()
            universe = s.sort(s.level('succ', 0))
            A = s.axiom('A', universe)
            a = s.axiom('a', A)
            fn_ty = s.pi(A, A)
            f = s.axiom('f', fn_ty)
            F = s.axiom('F', s.pi(fn_ty, universe))
            eta = s.lam(A, s.app(f, s.expr('bvar', 0)) if correct else a)
            left, right = s.app(F, f), s.app(F, eta)
            if reverse:
                left, right = right, left
            x = s.axiom('x', left)
            s.definition('test', right, x)
            yield f'eta_{correct}_{reverse}', s, 0 if correct else 1

    # Same function applied to proofs of different propositions must be rejected.
    s = Stream()
    P, Q = s.axiom('P', s.sort()), s.axiom('Q', s.sort())
    p, q = s.axiom('p', P), s.axiom('q', Q)
    F = s.axiom('F', s.pi(P, s.sort()))
    x = s.axiom('x', s.app(F, p))
    s.definition('test', s.app(F, q), x)
    yield 'different_propositions', s, 1

    # Both zero predicates must include max/imax expressions, not just .zero.
    for kind in ('max', 'imax'):
        s = Stream()
        level = s.level(kind, [0, 0])
        P = s.axiom('P', s.sort(level))
        p = s.axiom('p', P)
        t = s.definition('t', P, p, kind='thm')
        s.definition('test', P, t, kind='thm')
        yield f'theorem_zero_{kind}', s, 0

    # Native sort equivalence is deliberately weaker than isEquiv'.
    for complete_only in (False, True):
        s = Stream()
        u = s.level('param', s.name('u'))
        v = s.level('param', s.name('v'))
        lhs = s.level('max', [u, v])
        rhs = s.level('imax', [u, lhs]) if complete_only else s.level('max', [v, u])
        s.axiom('a', s.sort(lhs), params=('u', 'v'))
        a = s.const('a', (u, v))
        s.definition('test', s.sort(rhs), a, params=('u', 'v'))
        yield f'native_sort_{complete_only}', s, 1 if complete_only else 0

    # Constant universe lists use the complete algorithm instead.
    s = Stream()
    u = s.level('param', s.name('u'))
    v = s.level('param', s.name('v'))
    w = s.level('param', s.name('w'))
    lhs = s.level('max', [u, v])
    rhs = s.level('imax', [u, lhs])
    s.axiom('A', s.sort(w), params=('w',))
    s.axiom('a', s.const('A', (lhs,)), params=('u', 'v'))
    s.definition('test', s.const('A', (rhs,)), s.const('a', (u, v)), params=('u', 'v'))
    yield 'complete_constant_levels', s, 0

    for lh, rh in [('abbrev', 'abbrev'), ('opaque', 'abbrev'), ('abbrev', 'opaque'),
                   ({'regular': 2}, {'regular': 3}), ({'regular': 3}, {'regular': 2}),
                   ({'regular': 2}, {'regular': 2})]:
        for equal in (False, True):
            s = Stream()
            universe = s.sort(s.level('succ', 0))
            A, B = s.axiom('A', universe), s.axiom('B', universe)
            L = s.definition('L', universe, A, hints=lh)
            R = s.definition('R', universe, A if equal else B, hints=rh)
            x = s.axiom('x', L)
            s.definition('test', R, x)
            yield f'delta_{len(s.records)}_{lh}_{rh}_{equal}', s, 0 if equal else 1

    # The regular-definition shortcut first compares arguments. If that fails,
    # unfolding can still establish equality by discarding the argument.
    for proof_args in (False, True):
        for erase in (False, True):
            s = Stream()
            universe = s.sort(s.level('succ', 0))
            A = s.axiom('A', s.sort() if proof_args else universe)
            B = s.axiom('B', universe)
            a, b = s.axiom('a', A), s.axiom('b', A)
            F = s.axiom('F', s.pi(A, universe))
            body = B if erase else s.app(F, s.expr('bvar', 0))
            K = s.definition('K', s.pi(A, universe), s.lam(A, body), hints={'regular': 3})
            ka, kb = s.app(K, a), s.app(K, b)
            x = s.axiom('x', s.pi(ka, ka))
            s.definition('test', s.pi(kb, kb), x)
            yield f'regular_args_{proof_args}_{erase}', s, 0 if proof_args or erase else 1

    # A dependent let remains available to inference and reduces when demanded.
    for nondep in (False, True):
        s = Stream()
        universe = s.sort(s.level('succ', 0))
        A = s.axiom('A', universe)
        x = s.axiom('x', A)
        b = s.expr('bvar', 0)
        identity = s.lam(b, s.expr('bvar', 0))
        val = s.expr('letE', {'name': 0, 'type': universe, 'value': A, 'body': identity, 'nondep': nondep})
        s.definition('test', A, s.app(val, x))
        yield f'dependent_let_{nondep}', s, 0

    for opaque in (False, True):
        s = Stream()
        universe = s.sort(s.level('succ', 0))
        A = s.axiom('A', universe)
        X = s.definition('X', universe, A, kind='opaque' if opaque else 'def')
        x = s.axiom('x', X)
        s.definition('test', A, x)
        yield f'opaque_{opaque}', s, 1 if opaque else 0


    # A compact shared DAG represents a binary tree with 2**35 leaves.
    # Validation must retain sharing and still reject an undeclared universe.
    for allowed in (True, False):
        s = Stream()
        u = s.level('param', s.name('u'))
        s.axiom('A', s.sort(u), params=('u',))
        A = s.const('A', (u,))
        s.axiom('point', A, params=('u',))
        s.axiom('combine', s.pi(A, s.pi(A, A)), params=('u',))
        f = s.const('combine', (u,))
        term = s.const('point', (u,))
        for _ in range(35):
            term = s.app(s.app(f, term), term)
        s.definition('test', A, term, params=('u',) if allowed else ())
        yield f'shared_parameter_dag_{allowed}', s, 0 if allowed else 1


def run(check):
    count = 0
    for name, s, expected in cases():
        try:
            check(s.text(), expected)
        except AssertionError as exc:
            raise AssertionError(name) from exc
        count += 1
    print(f'{count} focused kernel regressions passed')


if __name__ == '__main__':
    root = Path('tests/generated/kernel')
    root.mkdir(parents=True, exist_ok=True)
    for old in root.glob('*.ndjson'):
        old.unlink()
    for i, (name, s, expected) in enumerate(cases()):
        safe_name = ''.join(c if c.isalnum() or c == '_' else '-' for c in name)
        (root / f'{i:03}_{expected}_{safe_name}.ndjson').write_text(s.text())
