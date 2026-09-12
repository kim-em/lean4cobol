# lean4cobol: a Lean 4 kernel in COBOL

Status: plan only (2026-09-12). Nothing implemented yet.

## Goal

Port the executable kernel of lean4lean (Mario Carneiro's Lean 4 reimplementation of
the Lean kernel, about 4.4k lines of Lean) to COBOL, targeting GnuCOBOL 3.2, and check
Lean Kernel Arena exports with it. Required scope: the `tutorial/*` suite and
`init-prelude`. Stretch: `init` (54k declarations). Everything larger is declined
(exit 2), which the arena does not penalise.

No verification story; this is the esoteric-language entry. As far as the survey found,
there is no type checker of any kind written in COBOL (the closest prior art is Cisp, a
Lisp interpreter), so completeness on `init-prelude` would be a first.

## Sources

- lean4lean, branch `arena`, commit bce3448, clone at
  `~/con-leche/_tmp/lean4lean` (Lean toolchain v4.33.0-rc2).
  https://github.com/digama0/lean4lean
- Lean Kernel Arena, clone at `~/con-leche/_tmp/lean-kernel-arena`; `lka.py build-test`
  produces the NDJSON streams, `lka.py run` scores a checker.
  https://github.com/leanprover/lean-kernel-arena
- lean4export NDJSON format 3.1. https://github.com/leanprover/lean4export
- GnuCOBOL 3.2 (via `nix shell nixpkgs#gnucobol`). https://gnucobol.sourceforge.io/
- Cisp, a Lisp in COBOL, for idioms. https://github.com/lauryndbrown/Cisp

## What is being ported

| file | lines | role |
|---|---|---|
| `Lean4Lean/TypeChecker.lean` | 979 | inferType, whnfCore, whnf, lazy delta, isDefEq, caches, Nat and String literal reduction |
| `Lean4Lean/Inductive/Add.lean` | 776 | positivity, universe checks, recursor generation, nested inductive elimination |
| `Lean4Lean/Inductive/Reduce.lean` | 109 | iota, K-like reduction, struct eta on the major premise |
| `Lean4Lean/Level.lean` | 363 | universe level normal form and `isEquiv`/`geq` |
| `Lean4Lean/Quot.lean` | 120 | quotient checks and `Quot.lift` reduction |
| `Lean4Lean/Environment.lean`, `Environment/Basic.lean` | 257 | addDecl per declaration kind |
| `Lean4Lean/Primitive.lean` | 492 | shape checks for `Nat`, `Bool`, `Eq` and the Nat primitives |
| `Lean4Lean/EquivManager.lean` | 64 | union-find defeq cache |
| `Lean4Lean/Replay.lean`, `Main.lean` | 500 | driver: topological replay, constructor/recursor regeneration and comparison, skipping `unsafe`/`partial` |

Plus the core `Lean.Expr` operations lean4lean gets from C++ and the port writes by
hand: `instantiate`, `instantiateRev`, `instantiate1`, `abstract`, `abstractRange`,
`hasLooseBVars`, `looseBVarRange`, `instantiateLevelParams`, `Expr.replace`,
`Expr.eqv` (alpha equivalence ignoring binder names), `Expr.hash`, and the per-node
cached data (hash, loose-bvar range, has-fvar and has-level-param bits).

lean4lean's `divergences.md` and `bugs-found.md` document where it differs from the C++
kernel; the port follows lean4lean.

## GnuCOBOL features the design relies on

- `PROGRAM-ID. name RECURSIVE.` with `LOCAL-STORAGE SECTION` for per-invocation
  locals: this is how `inferType`/`whnf`/`isDefEq` recurse. GnuCOBOL compiles to C, so
  depth is bounded by the C stack; run under `ulimit -s unlimited`.
- `ALLOCATE`/`FREE`, `POINTER`, `BASED` items, `SET ADDRESS OF`: used only to grow
  arena tables by doubling (allocate, copy, free); never for node-level allocation.
- `COMP-5` binary items (32- and 64-bit) for handles, hashes and counters.
- `OCCURS ... DEPENDING ON` tables for arenas whose size is fixed per run, sized from a
  first pass over the input (the input file length bounds the node count).
- `INSPECT`, `UNSTRING`, reference modification `X(i:n)` for the byte scanner.
- `STOP RUN RETURNING n` / `MOVE n TO RETURN-CODE` for the arena's exit codes
  (0 accept, 1 reject, 2 decline, 3 error).
- Native decimal arithmetic up to 38 digits (`PIC 9(38)`), which the bignum module
  builds on.

## Design decisions

- **Arena of records with integer handles.** One `01`-level table per node kind
  (`NAME-ARENA`, `LEVEL-ARENA`, `EXPR-ARENA`, `CONST-ARENA`, `BIGNUM-LIMBS`,
  `STRING-BYTES`), each an `OCCURS` group with the fields lean4lean's structures carry:
  for `EXPR`, `EXPR-KIND PIC 9 COMP-5`, `EXPR-A`, `EXPR-B`, `EXPR-C PIC 9(9) COMP-5`,
  `EXPR-HASH PIC 9(18) COMP-5`, `EXPR-LBVR PIC 9(9) COMP-5`, `EXPR-FLAGS`. Handles are
  1-based subscripts; 0 is null.
- **Interning** for names, levels and expressions through open-addressing hash tables
  held as parallel `OCCURS` tables (`HT-KEY`, `HT-VAL`), one per arena, hashed with
  multiply-add on `COMP-5` items. Interned expressions make `eqv` on equal handles a
  single compare and let every cache be keyed by handle.
- **Caches** as in lean4lean's `State`: two infer caches, whnfCore, whnf, the
  union-find `EquivManager`, the `isDefEq` failure set, the unfold cache. All are
  handle-keyed hash tables; a cache miss policy identical to lean4lean's.
- **Bignums** as arrays of `PIC 9(9)` decimal limbs (base 10^9) with `COMPUTE` on
  `PIC 9(18)` intermediates; this is COBOL's native strength and reads naturally.
  Implement lean4lean's `reduceNat` set: add, sub, mul, div, mod, gcd, beq, ble, land,
  lor, xor, shiftLeft, shiftRight, pow (exponent cap 2^24), log2. The bitwise ones
  convert to binary limbs internally. Cross-check against the Lean reference on random
  inputs (a small `tests/nat.lean` generates cases).
- **Strings** expanded to `String.mk` of a `Char` list on demand, as lean4lean does.
- **Parser**: read the NDJSON file as `ORGANIZATION LINE SEQUENTIAL` with a large
  record (`PIC X(4000000)`; lean4export lines for `init-prelude` are far shorter, but
  measure the longest line in `init` before fixing the size, or fall back to
  `ORGANIZATION SEQUENTIAL` with `RECORD VARYING` and a manual newline scan). A
  hand-written scanner over the record buffer for the lean4export subset; no general
  JSON.
- **Replay**: keep lean4lean's driver behaviour (topological order, regenerate
  constructors and recursors and compare, skip `unsafe`/`partial`) so verdicts match
  lean4lean exactly.
- **Fuel**: `recDepth` and the loop fuels from `FuelConfig.lean`; running out is a
  decline, never a reject.
- **Structure**: one program per lean4lean file (`LEVEL`, `EXPR-OPS`, `TYPE-CHECKER`,
  `INDUCTIVE`, `QUOT`, `PRIMITIVE`, `REPLAY`, `PARSER`, `BIGNUM`, `HASHTAB`) as nested
  or separately compiled programs with `COPY` books for the arena layouts, so the port
  can be read next to the Lean source.

## Milestones

- M0: build with `cobc -x`, read a stream, count records; `NAME` and `LEVEL` arenas with
  interning; port `Level.lean` and check `isEquiv` on the level tests from lean4lean's
  `Tests/`. Exit-code plumbing done and tested first (reject vs error confusion is what
  the arena scores harshly).
- M1: `EXPR` arena with cached data and the ten Expr operations. Test: tutorial `001`
  to `005`.
- M2: `TypeChecker.lean`: inferType, whnfCore, whnf, lazy delta, isDefEq with caches.
  Test: the tutorial tests that need no inductives; `corner-cases/*` that apply.
- M3: `Inductive/*`, `Quot.lean`, `Primitive.lean`. Test: whole tutorial, static reject
  tests (`bogus1`, `orphan-*`, `rec-k-lie`, `proj-*`, ...).
- M4: bignums and string literals. Test: `init-prelude` accepted, `nat-rec-*` tests.
- M5: `init` under `ulimit -v 16000000` and `timeout`; profile with `perf stat -e
  instructions:u` for the record; register as a local arena checker
  (`arena/lean4cobol.yaml`) with `declines:` for `std`, `mathlib`, `cedar`, `cslib`,
  `con-leche`.
- M6: README with the results table and what COBOL made easy or hard.

## Testing

- `tests/run-arena.sh` wraps `lka.py run --checker lean4cobol` over the built streams.
- Differential: verdict per test against lean4lean's arena build for every test not
  declined.
- Unit tests for the level algebra and bignums, generated from Lean (`tests/*.lean`
  emit cases; the COBOL side reads them as fixed-format records).

## Success criteria

1. Tutorial suite: every verdict matches lean4lean.
2. `init-prelude` accepted, the static reject tests rejected, no crashes (exit 3) on the
   full 200-test run.
3. Stretch: `init` accepted within the arena's limits.

## Risks

- Line length and file handling for larger exports; settle the input strategy in M0.
- Recursion depth under `cobc`-generated C; `ulimit -s` and, if needed, an explicit stack
  for the `whnf` loop.
- Hash-table throughput in interpreted-feeling COBOL arithmetic; `COMP-5` everywhere in
  the hot path, decimal only in the bignum module.
- Fidelity is by verdict agreement with lean4lean, not proof.
