# lean4cobol

A GnuCOBOL 3.2 port of lean4lean's executable Lean 4 kernel, following
reference revision `bce3448115f7819fc12d647fadd3bb090666637e`.

Build with the toolchain pinned in `flake.lock`:

```sh
nix develop --ignore-environment -c make
ulimit -s unlimited
bin/lean4cobol input.ndjson
```

With GnuCOBOL 3.2, a C compiler, GNU Make and Python 3 installed, use `make`.
The checker is implemented in COBOL. Python prepares the release build's
helper entry declarations; Lean is used only for test/reference tooling and
regenerating fixed quotations.

Mathlib accepts in **4 h 19 m 37 s**, using **7.09 GiB peak resident memory**.
The pinned lean4lean reference accepts the same export in 1 h 10 m 48 s.
All **211 measured arena inputs** agree with the reference, including the
142 tutorial and 25 performance cases. See [performance](docs/performance.md)
for measurements and timing caveats, and [case results](docs/results.json).
No libraries are configured to be declined without checking.

The kernel includes dependent functions, nested and mutual inductives,
constructor/recursor regeneration, projections, structure equality, quotients,
primitive defining-equation checks, and arbitrary-precision natural arithmetic.
String literals expand for equality and reduction, including Unicode decoding.
See [architecture](docs/architecture.md) for the representation and cache rules.

The launcher has no wall-clock timeout. Exit codes are 0 for acceptance,
1 for rejection, 2 for resource/feature decline, and 3 for operational errors.
Lines above 4,000,000 bytes and JSON nesting beyond 512 levels decline.
Input is streamed without a whole-file size limit; internal resource guards
still apply. `--scan` only parses and interns the export and does not check proofs.

```sh
nix develop --ignore-environment -c make test
nix develop --ignore-environment -c make debug
```

Debug and release builds use separate directories. `make` selects the release
executables at `bin/`; `make debug` selects and tests the checked executables.
See [testing](docs/testing.md) for reference comparisons and arena commands.

Prepare the pinned upstream arena entry after committing the source:

```sh
python3 scripts/prepare-arena-submission.py --revision HEAD
```

This writes the YAML, patch and PR body to `_tmp/arena-submission/`.
Publish that source revision before submitting the patch to
`leanprover/lean-kernel-arena`.

Licensed under Apache-2.0; see [NOTICE](NOTICE) for attribution.
