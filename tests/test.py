"""End-to-end parser/exit-code regressions; no reference checker at runtime."""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

from test_fast_parser import run as test_fast_parser
from test_hash import run as test_hash
from test_levels import run as test_levels
from test_expr import run as test_expr
from test_kernel import run as test_kernel
from test_inductive import run as test_inductive
from test_primitive import run as test_primitive
from test_nested import run as test_nested
from test_nat import run as test_nat
from test_arithmetic import run as test_arithmetic
from test_strings import run as test_strings
from test_well_founded import run as test_well_founded
from test_spines import run as test_spines

HEADER = {'meta': {'exporter': {'name': 'test', 'version': '1'},
                   'format': {'version': '3.1.0'},
                   'lean': {'version': '4.33.0-rc2', 'githash': '0' * 40}}}


def stream(*records):
    return '\n'.join(json.dumps(x, ensure_ascii=False) for x in (HEADER,) + records) + '\n'


def check(data, expected, scan=False, contains=None):
    if isinstance(data, str):
        data = data.encode()
    with tempfile.NamedTemporaryFile() as f:
        f.write(data)
        f.flush()
        p = subprocess.run(['bin/lean4cobol'] + (['--scan'] if scan else []) + [f.name],
                           capture_output=True, timeout=15)
    assert expected is None or p.returncode == expected, (expected, p.returncode, p.stdout, p.stderr, data[:500])
    if contains is not None:
        assert contains.encode() in p.stdout, (contains, p.stdout)
    return p


def expression_parser_tests():
    base = [
        {'in': 1, 'str': {'pre': 0, 'str': 'u'}},
        {'in': 2, 'str': {'pre': 0, 'str': 'A'}},
        {'in': 3, 'str': {'pre': 0, 'str': 'x'}},
        {'il': 1, 'param': 1}, {'il': 2, 'succ': 0},
        {'ie': 0, 'sort': 0}, {'ie': 1, 'sort': 2}, {'ie': 2, 'bvar': 0},
    ]
    lam = {'name': 3, 'type': 0, 'body': 2, 'binderInfo': 'default'}
    lets = {'name': 3, 'type': 0, 'value': 1, 'body': 2, 'nondep': False}
    good = [
        {'ie': 3, 'lam': lam},
        {'ie': 4, 'lam': {**lam, 'name': 2, 'binderInfo': 'implicit'}},
        {'ie': 5, 'forallE': lam},
        {'ie': 6, 'letE': lets},
        {'ie': 7, 'letE': {**lets, 'nondep': True}},
        {'ie': 8, 'natVal': '00012'}, {'ie': 9, 'natVal': '12'},
        {'ie': 10, 'strVal': '12'},
        {'ie': 11, 'mdata': {'expr': 1, 'data': {}}},
        {'ie': 12, 'const': {'name': 2, 'us': [0, 1, 0]}},
        {'ie': 13, 'const': {'name': 2, 'us': [0, 1, 0]}},
        {'ie': 14, 'proj': {'typeName': 2, 'idx': 0, 'struct': 3}},
        {'ie': 15, 'app': {'fn': 3, 'arg': 0}},
    ]
    check(stream(*(base + good)), 0, contains='exprs=13 ')
    invalid = [
        {'bvar': -1}, {'bvar': 1.5}, {'sort': 50}, {'fvar': 1},
        {'const': {'name': 50, 'us': []}}, {'const': {'name': 1, 'us': [50]}},
        {'const': {'name': 1, 'us': [[0]]}}, {'const': {'name': 1, 'us': {}}},
        {'app': {'fn': 0, 'arg': 50}}, {'app': {'arg': 0}},
        {'lam': {**lam, 'name': 50}}, {'lam': {**lam, 'binderInfo': 'bad'}},
        {'forallE': {**lam, 'body': 50}}, {'letE': {**lets, 'nondep': 1}},
        {'proj': {'typeName': 2, 'idx': -1, 'struct': 0}},
        {'natVal': ''}, {'natVal': '1a'}, {'natVal': '+1'}, {'natVal': 1},
        {'strVal': True}, {'mdata': {'expr': 50, 'data': {}}},
        {'mdata': {'expr': 0, 'data': []}},
    ]
    for bad in invalid:
        check(stream(*(base + [{'ie': 3, **bad}])), 1)
    check(stream(*(base + [{'ie': 3, 'bvar': 2**32-1}])), 2)
    check(stream(*(base + [{'ie': 3, 'bvar': 2**32}])), 2)
    check(stream(*(base + [{'ie': 3, 'natVal': '9' * 10000}])), 0)
    # Replacements of export IDs must not mutate already-interned subexpressions.
    check(stream(*(base + good + [{'ie': 3, 'sort': 0}])), 0, contains='exprs=13 ')


    # A sparse ID is inserted before the dense prefix reaches it. Growing the
    # prefix must still find that entry; later replacement takes precedence.
    records = [{'in': 1, 'str': {'pre': 0, 'str': 'test'}},
               {'il': 1, 'succ': 0}, {'ie': 100, 'sort': 0}]
    records += [{'ie': i, 'sort': 1} for i in range(128) if i != 100]
    definition = {'def': dict(name=1, levelParams=[], type=0, value=100,
                             safety='safe', hints='abbrev', all=[1])}
    check(stream(*(records + [definition])), 0)
    check(stream(*(records + [{'ie': 100, 'sort': 1}, definition])), 1)
    huge = 18446744073709551615
    check(stream(*([{'ie': huge, 'sort': 0}, {'ie': 0, 'sort': 0},
                    {'ie': 1, 'forallE': {'name': 0, 'type': huge,
                     'body': 0, 'binderInfo': 'default'}}])), 0)


def kernel_tests():
    base = [
        {'in': 1, 'str': {'pre': 0, 'str': 'A'}},
        {'in': 2, 'str': {'pre': 0, 'str': 'B'}},
        {'in': 3, 'str': {'pre': 0, 'str': 'u'}},
        {'il': 1, 'succ': 0}, {'il': 2, 'param': 3},
        {'ie': 0, 'sort': 0}, {'ie': 1, 'sort': 1},
        {'ie': 2, 'const': {'name': 1, 'us': []}},
        {'ie': 3, 'const': {'name': 2, 'us': []}},
        {'ie': 4, 'bvar': 0}, {'ie': 5, 'sort': 2},
    ]
    def definition(name, value, ty=1, **extra):
        return {'def': dict(name=name, levelParams=[], type=ty, value=value,
                            safety='safe', hints='abbrev', all=[name]) | extra}
    def axiom(name=1, ty=0, **extra):
        return {'axiom': dict(name=name, levelParams=[], type=ty, isUnsafe=False) | extra}
    def go(expected, *records):
        return check(stream(*(base + list(records))), expected)
    go(0, definition(1, 0))
    go(1, definition(1, 1, ty=0))
    # A depends on B, although B is later in the export.
    go(0, definition(1, 3), definition(2, 0))
    go(1, definition(1, 3), definition(2, 2))
    go(1, definition(1, 2))
    go(1, axiom(ty=2))
    go(1, definition(1, 0), definition(1, 0))
    go(1, definition(1, 4))
    go(1, axiom(ty=4))
    go(1, axiom(ty=5))
    go(0, axiom(ty=5, levelParams=[3]))
    go(1, axiom(ty=5, levelParams=[3, 3]))
    go(0, definition(1, 4, safety='unsafe'))
    go(0, definition(1, 4, safety='partial'))
    go(0, axiom(ty=4, isUnsafe=True))
    go(1, definition(1, 0, safety='unsafe'), definition(2, 2))
    go(1, axiom(ty=5, levelParams=[3]), definition(2, 2, ty=0))
    go(1, definition(1, 0, hints='bad'))
    go(1, definition(1, 0, hints={'regular': -1}))
    go(1, definition(1, 0, all=[99]))
    go(1, {'thm': {'name': 1, 'levelParams': [], 'type': 1, 'value': 0, 'all': [1]}})
    # A lambda is not itself a type; the declared type must infer to a sort.
    go(1, {'ie': 6, 'lam': {'name': 1, 'type': 0, 'body': 4, 'binderInfo': 'default'}}, axiom(ty=6))


def run():
    test_hash()
    test_fast_parser(check, HEADER)
    test_levels()
    test_expr()
    expression_parser_tests()
    kernel_tests()
    test_kernel(check)
    test_inductive(check)
    test_primitive(check)
    test_nested(check)
    test_nat()
    test_arithmetic(check)
    test_strings(check)
    test_well_founded(check)
    test_spines(check)
    fuel_cases = Path('tests/fixtures/fuel/cases.txt').read_bytes()
    subprocess.run(['bin/expr-test'], input=fuel_cases, check=True, timeout=15)
    check(stream(), 0)
    check('', 1)
    check('{}', 1)
    check(stream({'axiom': {}}), 1)
    check(stream({'ie': 0, 'sort': 0}), 0)
    check(stream({'in': 1, 'str': {'pre': 99, 'str': 'a'}}), 1)
    check(stream({'il': 1, 'succ': 99}), 1)
    check(stream({'il': 1, 'max': [0]}), 1)
    check(stream({'il': 1, 'max': [0, 0, 0]}), 1)
    check(stream({'il': 1, 'max': [0, '0']}), 1)
    check(stream({'il': 1, 'param': 99}), 1)
    check(stream({'in': 1, 'str': {'pre': 0, 'str': 3}}), 1)
    check(stream({'in': 1, 'num': {'pre': 0, 'i': -1}}), 1)
    check(stream({'in': 1, 'num': {'pre': 0, 'i': 2**64}}), 2)
    check(stream({'meta': {}}), 1)
    check(json.dumps({'meta': {'format': {'version': '9.0.0'}}}), 2)
    for invalid in ['{', '{"in":1,}', '{"in":01}', '{"in":1.}',
                    '{"in":1e}', '{"in":+1}', '{"in":NaN}', '{"in":null,}',
                    '[1]', 'null', 'true', 'false', '1', '{"x":[1,]}',
                    '{"x":tru}', '{"x":fals}', '{"x":nul}', '{"x":true}junk',
                    r'{"x":"\q"}', r'{"x":"\uD800"}', r'{"x":"\uDC00"}',
                    r'{"x":"\uD800\u0000"}', r'{"x":"\uXX00"}',
                    '{"x":"\t"}', '{"x":"unterminated}',
                    '{"in":1,"in":2,"str":{"pre":0,"str":"x"}}']:
        check(stream() + invalid, 1, scan=True)
    for invalid in [b'{"x":"\x80"}', b'{"x":"\xc0\xaf"}', b'{"x":"\xed\xa0\x80"}',
                    b'{"x":"\xf4\x90\x80\x80"}', b'{"x":"\xe0\x80\x80"}',
                    b'{"x":"\xc2x"}', b'{"x":"\xc2"}', b'{"x":"\x00"}']:
        check(stream().encode() + invalid, 1, scan=True)
    names = ['a', '', 'a ', ' a', 'é', 'λ', '😀', '\x00', '\b\f\n\r\t', '"\\/']
    records = []
    for i, name in enumerate(names, 1):
        records.append({'in': i * 10**12, 'str': {'pre': 0, 'str': name}})
        records.append({'in': i * 10**12 + 1, 'str': {'pre': 0, 'str': name}})
    # Raw UTF-8 and JSON escapes must intern to exactly the same name.
    escaped = '\n'.join(json.dumps(x, ensure_ascii=True) for x in records)
    check(stream(*records) + escaped, 0, contains=f'names={len(names) + 1} ')
    check(stream({'in': 1, 'num': {'pre': 0, 'i': 2**64 - 1}},
                 {'in': 2, 'str': {'pre': 1, 'str': 'child'}}), 0, contains='names=3 ')
    records = [{'in': 2, 'str': {'pre': 0, 'str': 'u'}},
               {'il': 100, 'param': 2}, {'il': 3, 'succ': 100},
               {'il': 88, 'max': [3, 100]}, {'il': 4, 'imax': [88, 100]},
               {'il': 999, 'imax': [88, 100]}]
    check(stream(*records), 0, contains='names=2 levels=5 ')
    # Force arena/table growth and preserve parents across every reallocation.
    records = [{'in': i, 'str': {'pre': i-1, 'str': f'name{i}'}} for i in range(1, 1000)]
    records += [{'il': i, 'succ': i-1} for i in range(1, 1000)]
    check(stream(*records), 0, contains='names=1000 levels=1000 ')
    rng = random.Random(4193)
    for _ in range(50):
        values = [None, True, False, -123.5e30, 'é😀\n', [], {}, 2**100]
        obj = {'ignored': [rng.choice(values) for _ in range(rng.randrange(1, 100))]}
        check(stream(obj), 0, scan=True)
    # Exact chunk boundaries, with and without the final newline.
    for length in (8191, 8192, 8193, 16384, 16385, 65535, 65536, 65537, 131072):
        line = '{"x":"' + 'a' * (length - 8) + '"}'
        assert len(line) == length
        check(stream() + line + '\n', 0, scan=True, contains='records=2 ')
        check(stream() + line, 0, scan=True, contains='records=2 ')
    check(stream({'x': 'a' * 3999990}), 0, scan=True)
    check(stream({'x': 'a' * 4000000}), 2, scan=True)
    check(stream() + '{"x":' + '['*514 + '0' + ']'*514 + '}', 2, scan=True)
    check(stream().replace('\n', '\r\n'), 0)
    check(stream().rstrip('\n'), 0)
    with tempfile.NamedTemporaryFile() as f:
        f.write(b'invalid\n')
        f.truncate(6000000000)
        f.flush()
        p = subprocess.run(['bin/lean4cobol', f.name], capture_output=True)
        assert p.returncode == 1, p
    p = subprocess.run(['bin/lean4cobol', '/definitely/missing/lean4cobol.ndjson'], capture_output=True)
    assert p.returncode == 3, p
    p = subprocess.run(['bin/lean4cobol'], capture_output=True)
    assert p.returncode == 3, p
    print('parser, interning, Unicode, line limits, and exit-code tests passed')


if __name__ == '__main__':
    run()
