#!/usr/bin/env python3
"""Independent Python-integer oracle for decimal limb arithmetic."""
import math
import random
import subprocess
import sys
sys.set_int_max_str_digits(100000)
from pathlib import Path


def cases():
    rng = random.Random(903172)
    edge = [0, 1, 2, 29, 30, 31, 2**30 - 1, 2**30, 10**9 - 1, 10**9,
            10**9 + 1, 2**64 - 1, 2**64, 10**18 - 1, 10**18, 10**18 + 1,
            10**45 - 1, 10**45, 10**45 + 1, 2**255 - 1, 2**256]
    pairs = [(a, b) for a in edge for b in edge]
    pairs += [(rng.getrandbits(rng.randrange(1, 2049)),
               rng.getrandbits(rng.randrange(1, 2049))) for _ in range(100)]
    for a, b in pairs:
        answers = [a + b, max(a - b, 0), a * b, a // b if b else 0,
                   a % b if b else a, math.gcd(a, b), int(a == b), int(a <= b),
                   a & b, a | b, a ^ b]
        for op, value in enumerate(answers, 1):
            yield f'{op} {a} {b} {value}'
    for a in edge + [rng.getrandbits(2048) for _ in range(8)]:
        for b in [0, 1, 2, 28, 29, 30, 31, 59, 60, 61, 256, 1000]:
            yield f'12 {a} {b} {a << b}'
            yield f'13 {a} {b} {a >> b}'
        yield f'13 {a} {10**100} 0'
        yield f'15 {a} 0 {max(a.bit_length() - 1, 0)}'
        for b in [0, 1, 2, 3, 10, 31]:
            yield f'14 {a} {b} {a**b}'
    # Carry/borrow chains, long quotient, sparse limbs, and output allocation.
    a, b = 10**1800 - 1, 10**900 + 1
    yield f'1 {a} 1 {a+1}'
    yield f'2 {a+1} 1 {a}'
    yield f'4 {a} {b} {a//b}'
    yield f'5 {a} {b} {a%b}'
    for a in [0, 1]:
        yield f'14 {a} {2**24} {a}'
    yield f'12 0 {10**100} 0'
    yield f'12 1 {10**100} decline'
    yield f'14 2 {2**24} decline'
    # Force the arithmetic-work bound independently of the allocation bound.
    yield f'4 {10**30000 - 1} {10**15000 + 1} decline'
    yield '1 1 1 2'  # A declined call must release scratch and allow a new call.


def run():
    data = '\n'.join(cases()) + '\n'
    Path('tests/generated').mkdir(parents=True, exist_ok=True)
    Path('tests/generated/nats-python.txt').write_text(data)
    p = subprocess.run(['bin/nat-test'], input=data, text=True, capture_output=True, timeout=120)
    assert p.returncode == 0, p.stdout + p.stderr
    print(p.stdout.strip() + ' (independent Python oracle)')


if __name__ == '__main__':
    run()
