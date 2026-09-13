# lean4cobol

A port of lean4lean's executable Lean 4 kernel to GnuCOBOL 3.2, following
reference revision `bce3448115f7819fc12d647fadd3bb090666637e`.
The required [PLAN.md](PLAN.md) targets are implemented and validated;
[docs/progress.md](docs/progress.md) records the implementation audit.

Build and test with GnuCOBOL 3.2, a C compiler, Make, and Python 3:

```sh
nix shell nixpkgs#gnucobol nixpkgs#gcc nixpkgs#python3 -c make test
nix shell nixpkgs#gnucobol nixpkgs#gcc nixpkgs#python3 -c make debug
```

With those tools already installed, use `make test`. Python and Lean are used
for tests and regenerating fixed quotations; the checker executable contains
the COBOL implementation.

```sh
ulimit -s unlimited
bin/lean4cobol input.ndjson
bin/lean4cobol --scan input.ndjson
```

All **142 tutorial verdicts match** the pinned lean4lean reference (93 accepts,
49 rejects), with no declines or crashes. The checker now includes nested and mutual
inductives, regenerated constructors/recursors, projections, structure equality,
quotients, primitive defining-equation checks, and arbitrary-precision natural arithmetic
alongside the dependent-function core. String literals expand for equality,
projection and recursor reduction, including Unicode scalar decoding.

**Mathlib accepts in 4 h 19 m 37 s**, using 7.09 GiB peak resident memory.
The pinned lean4lean reference accepts the same export in 1 h 10 m 48 s.
The launcher has no wall-clock timeout. Current results cover **211 reference
matches and four declared declines**, including all 25 performance cases.
See [the Mathlib performance report](docs/mathlib-performance.md) for the
optimizations, exact measurements and shared-host timing caveats.

Historical measurements from the earlier, time-limited executable (2026-09-12):

| Suite | Result |
| --- | --- |
| Tutorial (142 cases) | 142 reference matches: 93 accepts, 49 rejects |
| `init-prelude` | Accepted in 4.28 s; 57.5 MiB peak RSS |
| Full arena (215 cases) | 206 reference matches; 9 declines; no wrong verdicts or errors |
| `init` (stretch target) | Declined at the 600 s wall limit |

That baseline configured five declines for `std`, `mathlib`, `cedar`, `cslib`, and
`con-leche`. The other four are `init` and three performance cases that reached
the expression-arena bound: `perf/app-lam`, `perf/magma-list-deep-n36`, and
`perf/magma-list-pair-n21`. All 206 non-declined results agree with the pinned
reference, including the arena's 15 cases labelled “either.”

The release and bounds-checking regression suites pass. Focused coverage
includes 31 well-founded primitive cases, 28 binder/application cases, and
544 reference-generated fuel checks. The full results and measured source
hashes are saved in [docs/results.json](docs/results.json), with a
[CSV table](docs/results.csv). [Performance notes](docs/build-performance.md)
record the `init` instruction profile, environment, and COBOL implementation
tradeoffs.

`--scan` parses and interns the stream without checking declaration types or
proofs; a successful scan does **not** certify any proof.

Exit codes are 0 for accept, 1 for reject, 2 for unsupported features or resource
limits, and 3 for operational errors such as an unreadable input file. Lines above
4,000,000 bytes and JSON nesting beyond 512 levels decline. Raw file blocks are split into lines in COBOL, preserving every input byte.
Input is streamed without a whole-file size limit.
Sparse external IDs use a hash table rather than allocating up to the largest ID.

Universe comparisons can also be tested against the pinned lean4lean revision:

```sh
tests/reference-levels.sh
tests/reference-exprs.sh
tests/reference-primitive-quotes.sh
tests/reference-nats.sh
tests/reference-fuel.sh
```

This prepares a reference checkout under `_tmp/`, builds the required Lean modules,
generates cases for universe algorithms, expression operations and Nat arithmetic, and runs the COBOL
unit drivers. Set
`LEAN4LEAN_REFERENCE` to use an existing checkout at the pinned revision.

For a local arena checkout with built streams:

```sh
tests/run-arena.sh --test 'tutorial/*'
# Run the whole built suite and compare fresh results with the pinned reference:
tests/run-arena.sh
python3 tests/compare-arena.py
```

Set `LEAN_KERNEL_ARENA` for a checkout outside `_tmp/arena`. The wrapper registers
this worktree using `arena/lean4cobol.yaml` and invokes `lka.py run`. For direct reference
comparison, run `python3 tests/differential.py`; this fails on any mismatch,
error, or decline. `--allow-declines` enables partial development checks.

Focused tests that exercise the kernel without inductives can also be compared:

```sh
python3 tests/test_kernel.py
python3 tests/differential.py --suite tests/generated/kernel --output tests/generated/kernel-differential.json
python3 tests/test_inductive.py
python3 tests/differential.py --suite tests/generated/inductive --output tests/generated/inductive-differential.json
python3 tests/test_primitive.py
python3 tests/differential.py --suite tests/generated/primitive --output tests/generated/primitive-differential.json
python3 tests/test_strings.py
python3 tests/differential.py --suite tests/generated/strings --output tests/generated/strings-differential.json
python3 tests/test_spines.py
python3 tests/differential.py --suite tests/generated/spines --output tests/generated/differential-spines.json
python3 tests/test_well_founded.py
python3 tests/differential.py --suite tests/generated/well-founded --output tests/generated/differential-well-founded.json
python3 tests/test_arithmetic.py
python3 tests/differential.py --suite tests/generated/arithmetic --output tests/generated/arithmetic-differential.json
python3 tests/test_nested.py
python3 tests/differential.py --suite tests/generated/nested --output tests/generated/nested-differential.json
```

The code is licensed under Apache-2.0; see [NOTICE](NOTICE) for attribution.
