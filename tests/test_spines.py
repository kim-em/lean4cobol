"""Dependent substitutions across binder/application groups and reduction boundaries."""
from pathlib import Path
from test_kernel import Stream


def cases():
    for wrapper in ('plain', 'metadata', 'let', 'definition'):
        for select in (0, 1):
            for correct in (False, True):
                s = Stream()
                U = s.sort(s.level('succ', 0))
                A, B = s.axiom('A', U), s.axiom('B', U)
                value = s.axiom('value', [B, A][select])
                fn = s.lam(U, s.lam(U, s.expr('bvar', select)))
                ty = s.pi(U, s.pi(U, U))
                if wrapper == 'metadata':
                    fn = s.expr('mdata', {'expr': fn, 'data': {}})
                elif wrapper == 'let':
                    fn = s.expr('letE', {'name': 0, 'type': ty, 'value': fn,
                                        'body': s.expr('bvar', 0), 'nondep': False})
                elif wrapper == 'definition':
                    fn = s.definition('chooseType', ty, fn)
                args = [A, B] if correct else [B, A]
                result = s.app(s.app(fn, args[0]), args[1])
                s.definition('test', result, value)
                yield f'beta_{wrapper}_{select}_{correct}', s, 0 if correct else 1

    # Reducing the first lambda reveals another lambda only after substituting
    # through metadata; a remaining argument must be reapplied and reduced.
    for correct in (False, True):
        s = Stream()
        U = s.sort(s.level('succ', 0))
        A, B = s.axiom('A', U), s.axiom('B', U)
        a = s.axiom('a', A)
        inner = s.lam(U, s.expr('bvar', 1))
        fn = s.lam(U, s.expr('mdata', {'expr': inner, 'data': {}}))
        result = s.app(s.app(fn, A if correct else B), B)
        s.definition('test', result, a)
        yield f'beta_reapply_{correct}', s, 0 if correct else 1

    # A raw forall prefix ends at a definition which reduces to another forall.
    # Comparing distinct inhabitants asks proof irrelevance for their inferred
    # types, exercising inference-only application substitution across that gap.
    for proposition in (False, True):
        s = Stream()
        U = s.sort(s.level('succ', 0))
        A = s.axiom('A', s.sort() if proposition else U)
        a = s.axiom('a', A)
        domain_sort = s.sort() if proposition else U
        arrow_sort = domain_sort
        arrow = s.definition('arrow', s.pi(domain_sort, arrow_sort),
                             s.lam(domain_sort, s.pi(s.expr('bvar', 0), s.expr('bvar', 1))))
        f = s.axiom('f', s.pi(domain_sort, s.app(arrow, s.expr('bvar', 0))))
        fa = s.app(s.app(f, A), a)
        family = s.axiom('family', s.pi(A, U))
        x = s.axiom('x', s.app(family, fa))
        s.definition('test', s.app(family, a), x)
        yield f'infer_app_delta_{proposition}', s, 0 if proposition else 1

    # Consecutive let locals depend on earlier local types and values. The
    # final inferred type retains only the let bindings needed by that type.
    for correct in (False, True):
        s = Stream()
        U = s.sort(s.level('succ', 0))
        A, B = s.axiom('A', U), s.axiom('B', U)
        a = s.axiom('a', A)
        inner = s.expr('letE', {'name': 0, 'type': s.expr('bvar', 0), 'value': a,
                               'body': s.expr('bvar', 0), 'nondep': False})
        val = s.expr('letE', {'name': 0, 'type': U, 'value': A,
                             'body': inner, 'nondep': False})
        s.definition('test', A if correct else B, val)
        yield f'dependent_let_group_{correct}', s, 0 if correct else 1

    # Heterogeneous, dependent binder domains expose reversed substitutions;
    # checking and equality must retain all outer locals until the final body.
    for length in (2, 8, 48):
        for correct in (False, True):
            s = Stream()
            U = s.sort(s.level('succ', 0))
            body = s.expr('bvar', 0 if correct else 1)
            ty = s.expr('bvar', length - 1)
            for i in reversed(range(1, length)):
                domain = s.expr('bvar', i - 1)
                body = s.lam(domain, body)
                ty = s.pi(domain, ty)
            body = s.lam(U, body)
            ty = s.pi(U, ty)
            # At length 2, the incorrect body returns the type itself;
            # at greater lengths all term arguments share that type, so use
            # the outer type variable to make the forged body ill typed.
            if not correct and length > 2:
                body = s.expr('bvar', length - 1)
                for i in reversed(range(1, length)):
                    body = s.lam(s.expr('bvar', i - 1), body)
                body = s.lam(U, body)
            s.definition('test', ty, body)
            yield f'lambda_group_{length}_{correct}', s, 0 if correct else 1


def run(check):
    count = 0
    for name, stream, expected in cases():
        try:
            check(stream.text(), expected)
        except AssertionError as exc:
            raise AssertionError(name) from exc
        count += 1
    print(f'{count} binder/application spine regressions passed')


if __name__ == '__main__':
    dest = Path('tests/generated/spines')
    dest.mkdir(parents=True, exist_ok=True)
    for old in dest.glob('*.ndjson'):
        old.unlink()
    for name, stream, expected in cases():
        (dest / f'{expected}_{name}.ndjson').write_text(stream.text())
