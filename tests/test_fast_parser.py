"""Compare fast-record parsing with the general parser, including mutations."""
import json
import random
import re


def run(check, header):
    base = json.dumps(header, separators=(',', ':')) + '\n'
    seed = '{"ie":0,"sort":0}\n{"ie":1,"bvar":2}\n'
    cases = ['{"ie":2,"app":{"fn":0,"arg":1}}',
             '{"ie":2,"sort":0}', '{"ie":2,"bvar":0}',
             '{"ie":2,"bvar":2147483647}',
             '{"ie":2147483648,"bvar":4294967294}',
             '{"ie":2,"app":{"fn":90,"arg":1}}']
    rng = random.Random(93)
    for original in cases[:3]:
        for _ in range(70):
            i = rng.randrange(len(original))
            replacement = rng.choice(['', '0', '9', '-', '+', ' ', '}', '"', ',', '\t'])
            cases.append(original[:i] + replacement + original[i + 1:])
    for record in cases:
        # Leading whitespace forces the general parser without changing JSON.
        slow = check(base + seed + ' ' + record + '\n', None, scan=True)
        fast = check(base + seed + record + '\n', slow.returncode, scan=True)
        if slow.returncode == 0:
            assert re.search(rb'exprs=\d+', slow.stdout)[0] == re.search(rb'exprs=\d+', fast.stdout)[0]
    print(f'{len(cases)} fast/general parser comparisons')
