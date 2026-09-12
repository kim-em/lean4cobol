"""Independent symbolic tests for binder-sensitive expression operations."""
from functools import lru_cache
import random
import subprocess

B = lambda i: ('bvar', i)
F = lambda i: ('fvar', i)
Z = ('zero',)
U = lambda i: ('param', i)
S = lambda u: ('sort', u)
APP = lambda f, a: ('app', f, a)


def children(e):
    return {'app': (1, 2), 'lam': (1, 2), 'forall': (1, 2),
            'let': (1, 2, 3), 'proj': (3,), 'mdata': (1,)}.get(e[0], ())


def under_binder(e, index):
    return (e[0] in ('lam', 'forall') and index == 2) or (e[0] == 'let' and index == 3)


def rewrite(e, fn, depth=0):
    replacement = fn(e, depth)
    if replacement is not None:
        return replacement
    out = list(e)
    for i in children(e):
        out[i] = rewrite(e[i], fn, depth + under_binder(e, i))
    return tuple(out)


def lift(e, amount):
    return rewrite(e, lambda e, d: B(e[1]+amount) if e[0] == 'bvar' and e[1] >= d else None)


def instantiate(e, values, reverse=False):
    values = list(reversed(values)) if reverse else values
    def subst(e, d):
        if e[0] != 'bvar' or e[1] < d:
            return None
        i = e[1] - d
        return lift(values[i], d) if i < len(values) else B(e[1] - len(values))
    return rewrite(e, subst)


def abstract(e, values):
    def subst(e, d):
        if e[0] == 'fvar':
            for i, v in enumerate(reversed(values)):
                if e == v:
                    return B(d+i)
        return None
    return rewrite(e, subst)


def level_subst(u, pairs):
    if not level_has_param(u) or not pairs:
        return u
    if u[0] == 'param':
        return next((val for key, val in pairs if key == u[1]), u)
    if u[0] == 'zero':
        return u
    args = [level_subst(v, pairs) for v in u[1:]]
    return smart_level(u[0], *args)


def smart_level(kind, a, b=None):
    def offset(u):
        k = 0
        while u[0] == 'succ':
            k += 1
            u = u[1]
        return u, k
    def positive(u):
        return u[0] == 'succ' or (u[0] == 'max' and (positive(u[1]) or positive(u[2]))) or (u[0] == 'imax' and positive(u[2]))
    def subsumes(u, v):
        return (offset(v)[0] == Z and offset(u)[1] >= offset(v)[1]) or (u[0] == 'max' and v in u[1:])
    if kind == 'imax':
        if positive(b):
            return smart_level('max', a, b)
        if b == Z or a == Z: return b
        if a == b: return a
    if kind == 'max':
        if a == b or b == Z: return a
        if a == Z: return b
        if subsumes(a, b): return a
        if subsumes(b, a): return b
        if offset(a)[0] == offset(b)[0]:
            return a if offset(a)[1] >= offset(b)[1] else b
    return (kind, a) if b is None else (kind, a, b)


def expr_level_subst(e, pairs):
    def subst(e, _):
        if e[0] == 'sort':
            return S(level_subst(e[1], pairs))
        if e[0] == 'const':
            return ('const', e[1], tuple(level_subst(u, pairs) for u in e[2]))
        return None
    return rewrite(e, subst)


@lru_cache(None)
def level_has_param(u):
    return u[0] == 'param' or (u[0] != 'zero' and any(level_has_param(v) for v in u[1:]))


@lru_cache(None)
def data(e):
    lbvr = e[1]+1 if e[0] == 'bvar' else 0
    fvar = e[0] == 'fvar'
    param = (e[0] == 'sort' and level_has_param(e[1])) or (
        e[0] == 'const' and any(level_has_param(u) for u in e[2]))
    for i in children(e):
        b, f, p = data(e[i])
        lbvr = max(lbvr, max(0, b-under_binder(e, i)))
        fvar |= f
        param |= p
    return lbvr, int(fvar), int(param)


def cases():
    rng = random.Random(57891)
    lines = []
    expr_ids, level_ids, list_ids = {}, {Z: 0}, {(): 0}
    next_expr = 1
    checks = 0

    def level(u):
        if u not in level_ids:
            k = {'succ': 1, 'max': 2, 'imax': 3, 'param': 4}[u[0]]
            a = u[1] if k == 4 else level(u[1])
            b = level(u[2]) if k in (2, 3) else 0
            n = len(level_ids)
            level_ids[u] = n
            lines.append(f'L {n} {k} {a} {b} 0 0')
        return level_ids[u]

    def levels(us):
        if us not in list_ids:
            a, b = level(us[0]), levels(us[1:])
            n = len(list_ids)
            list_ids[us] = n
            lines.append(f'S {n} {a} {b} 0 0 0')
        return list_ids[us]

    def emit(e):
        nonlocal next_expr, checks
        if e in expr_ids:
            return expr_ids[e]
        k = ['bvar', 'sort', 'const', 'app', 'lam', 'forall', 'let', 'proj',
             'nat', 'str', 'fvar', 'mdata'].index(e[0])
        args = [0, 0, 0, 0]
        if k in (0, 8, 9, 10): args[0] = e[1]
        elif k == 1: args[0] = level(e[1])
        elif k == 2: args[:2] = [e[1], levels(e[2])]
        elif k in (3, 4, 5): args[:2] = [emit(e[1]), emit(e[2])]
        elif k == 6: args = [emit(e[1]), emit(e[2]), emit(e[3]), e[4]]
        elif k == 7: args[:3] = [e[1], e[2], emit(e[3])]
        else: args[0] = emit(e[1])
        n = next_expr
        next_expr += 1
        expr_ids[e] = n
        lines.append(f'E {n} {k} ' + ' '.join(map(str, args)))
        checks += 1
        lines.append(f'D {checks} {n} ' + ' '.join(map(str, data(e))) + ' 0')
        return n

    def test(mode, e, pairs=(), amount=0):
        nonlocal next_expr, checks
        if mode == 0: expected = lift(e, amount)
        elif mode in (1, 2): expected = instantiate(e, [v for _, v in pairs], mode == 2)
        elif mode == 3: expected = abstract(e, [v for _, v in pairs])
        elif mode == 6: expected = abstract(e, [v for _, v in pairs][:amount])
        elif mode in (7, 8): expected = instantiate(e, [pairs[0][1]])
        elif mode == 4: expected = expr_level_subst(e, pairs)
        else: expected = rewrite(e, lambda x, _: next((v for k, v in pairs if k == x), None))
        eid, want = emit(e), emit(expected)
        vec = []
        for key, val in pairs:
            vec.extend([emit(key) if mode == 5 else key, level(val) if mode == 4 else emit(val)])
        got = next_expr
        next_expr += 1
        lines.append(f'T {got} {mode} {eid} {amount} {len(pairs)} 0 ' + ' '.join(map(str, vec)))
        checks += 1
        lines.append(f'C {checks} {got} {want} 0 0 0')

    us = [Z, U(1), U(2), ('succ', Z), ('imax', U(1), ('max', U(2), ('succ', U(1))))]
    atoms = [B(i) for i in range(5)] + [F(i) for i in range(1, 4)] + [S(u) for u in us]
    atoms += [('const', 1, tuple(us)), ('nat', 1), ('str', 2)]
    pool = atoms[:]
    for _ in range(700):
        tag = rng.choice(['app', 'lam', 'forall', 'let', 'proj', 'mdata'])
        sub = lambda: rng.choice(pool if rng.random() < 0.35 else atoms)
        if tag in ('app', 'lam', 'forall'): e = (tag, sub(), sub())
        elif tag == 'let': e = (tag, sub(), sub(), sub(), rng.randrange(2))
        elif tag == 'proj': e = (tag, 4, rng.randrange(4), sub())
        else: e = (tag, sub())
        pool.append(e)
    # Shared open subterms reached at distinct binding depths need distinct memo keys.
    shared = APP(B(1), F(1))
    pool += [APP(shared, ('lam', S(Z), shared)),
             ('let', B(0), B(1), APP(B(0), B(2)), 0),
             ('lam', B(0), ('lam', B(1), APP(B(0), B(3))))]
    for e in pool:
        emit(e)
        test(0, e, amount=rng.randrange(4))
        values = [(0, rng.choice(pool)) for _ in range(rng.randrange(4))]
        test(1, e, values)
        test(2, e, values)
        test(3, e, [(0, F(1)), (0, F(2)), (0, F(1)), (0, S(Z))][:rng.randrange(5)])
        test(6, e, [(0, F(1)), (0, F(2)), (0, F(1))], amount=rng.randrange(6))
        test(7, e, [(0, B(1))])
        test(8, e, [(0, B(1))])
        test(4, e, [(1, ('succ', U(2))), (2, Z), (1, U(3))])
        test(5, e, [(B(1), F(3)), (S(Z), B(2)), (shared, F(2))])
    return '\n'.join(lines) + '\n'


def run():
    p = subprocess.run(['bin/expr-test'], input=cases(), text=True, capture_output=True, timeout=60)
    assert p.returncode == 0, (p.returncode, p.stdout[-4000:], p.stderr)
    print(p.stdout.strip())
    # Deep structural recursion exhausts fuel with decline, never reject/error.
    fuel_case = "\n".join([
        'E 1 0 0 0 0 0', 'E 2 3 1 1 0 0', 'E 3 3 2 2 0 0',
        'F 0 1 0 0 0 0', 'T 4 0 3 1 0 0', ''])
    p = subprocess.run(['bin/expr-test'], input=fuel_case, text=True, capture_output=True)
    assert p.returncode == 2, (p.returncode, p.stdout, p.stderr)


if __name__ == '__main__':
    run()
