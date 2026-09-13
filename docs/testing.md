# Testing

Use the pinned toolchain for release and checked regressions:

```sh
nix develop --ignore-environment -c make test
nix develop --ignore-environment -c make debug
nix develop --ignore-environment -c make
```

The final command selects the release executables again. Modes use separate
directories under `bin/build/`, with public executable links under `bin/`.

Reference oracles prepare the pinned lean4lean checkout under `_tmp/`:

```sh
tests/reference-levels.sh
tests/reference-exprs.sh
tests/reference-primitive-quotes.sh
tests/reference-nats.sh
tests/reference-fuel.sh
```

Set `LEAN4LEAN_REFERENCE` to use an existing reference checkout. Fixture
manifests record their Lean toolchains, exporter revisions and input hashes.

For a Lean Kernel Arena checkout with built exports:

```sh
tests/run-arena.sh --test 'tutorial/*'
tests/run-arena.sh
python3 tests/compare-arena.py
```

Set `LEAN_KERNEL_ARENA` for a checkout outside `_tmp/arena`. The wrapper stages
the source and pinned build environment, builds the checker, and invokes the
official arena runner. No workloads are predeclared as declined. Comparison
requires fresh checker results and reruns the pinned reference without a
timeout unless `--timeout` is explicitly supplied. Use `--exclude` to omit
inputs measured separately.

`python3 tests/differential.py` compares generated fixtures directly with the
reference and fails on mismatches, errors or declines. Individual generators
such as `tests/test_kernel.py` write fixtures under `tests/generated/`; pass
that directory with `--suite` to compare a focused suite.

For direct whole-process measurements:

```sh
ulimit -s unlimited
perf stat -e instructions:u bin/lean4cobol input.ndjson
```

`LEAN4COBOL_PROGRESS=1` reports parse/replay progress, and
`LEAN4COBOL_TRACE=1` identifies a failing declaration. `--scan` does not check
declarations or proofs and must not be reported as kernel acceptance.
