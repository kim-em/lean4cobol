"""Independent integer oracle for the bounded native hash arithmetic."""
import random
import subprocess


def run():
    rng = random.Random(941)
    prime = 2147483647
    cases = [(h, a) for h in (0, 1, prime - 2, prime - 1)
             for a in (0, 1, prime - 1, prime, prime + 1,
                       2 * prime - 1, 2 * prime, 2 * prime + 1)]
    cases += [(rng.randrange(prime), rng.randrange(2**32)) for _ in range(20000)]
    data = ''.join(f'{h:010} {a:010}\n' for h, a in cases)
    proc = subprocess.run(['bin/hash-test'], input=data, text=True,
                          capture_output=True, check=True)
    assert list(map(int, proc.stdout.split())) == [(48271 * h + a) % prime for h, a in cases]
    print(f'{len(cases)} native hash checks (independent Python oracle)')


if __name__ == '__main__':
    run()
