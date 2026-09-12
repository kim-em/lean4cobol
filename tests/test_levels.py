"""Independent bounded semantic oracle for the COBOL universe algebra."""
import itertools
import random
import subprocess


def cases():
    nodes = [(0, 0, 0)]
    ids = {nodes[0]: 0}
    lines = []

    def node(k, a=0, b=0):
        key = (k, a, b)
        if key not in ids:
            ids[key] = len(nodes)
            nodes.append(key)
            lines.append(f'N {ids[key]} {k} {a} {b} 0')
        return ids[key]

    u, v, w, x = [node(4, n) for n in range(1, 5)]
    succ = lambda a: node(1, a)
    mx = lambda a, b: node(2, a, b)
    im = lambda a, b: node(3, a, b)
    two = succ(succ(0))
    checks = [
        (0, mx(v, mx(w, im(im(im(u, v), w), x))),
            mx(v, mx(w, im(im(im(u, w), v), x))), 1),
        (1, mx(two, v), im(two, v), 1),
        (1, mx(succ(succ(u)), v), im(succ(succ(u)), v), 1),
        (0, im(u, mx(u, v)), mx(u, v), 1),
        (0, mx(v, u), mx(im(u, v), u), 1),
        (0, im(0, u), u, 1),
        (0, im(two, u), mx(two, u), 0),
    ]
    by_size = {1: [0, u, v, w]}
    for size in range(2, 6):
        out = [succ(a) for a in by_size[size - 1]]
        for left_size in range(1, size - 1):
            for a in by_size[left_size]:
                for b in by_size[size - 1 - left_size]:
                    out.extend([mx(a, b), im(a, b)])
        by_size[size] = out
    valuations = list(itertools.product(range(8), repeat=3))
    values = []
    for k, a, b in nodes:
        if k == 0:
            val = (0,) * len(valuations)
        elif k == 4:
            val = tuple(v[a - 1] if a <= 3 else 0 for v in valuations)
        elif k == 1:
            val = tuple(v + 1 for v in values[a])
        elif k == 2:
            val = tuple(max(x, y) for x, y in zip(values[a], values[b]))
        else:
            val = tuple(max(x, y) if y else 0 for x, y in zip(values[a], values[b]))
        values.append(val)
    buckets = {}
    sample = [a for ls in by_size.values() for a in ls]
    for a in sample:
        representative = buckets.setdefault(values[a], a)
        checks.append((0, a, representative, 1))
    rng = random.Random(93457)
    for _ in range(5000):
        a, b = rng.choices(sample, k=2)
        checks.extend([(0, a, b, int(values[a] == values[b])),
                       (1, a, b, int(all(x >= y for x, y in zip(values[a], values[b]))))])
    for i, (mode, a, b, expected) in enumerate(checks):
        lines.append(f'C {i} {mode} {a} {b} {expected}')
    return '\n'.join(lines) + '\n'


def run():
    p = subprocess.run(['bin/level-test'], input=cases(), text=True, capture_output=True)
    assert p.returncode == 0, (p.returncode, p.stdout, p.stderr)
    print(p.stdout.strip())


if __name__ == '__main__':
    run()
