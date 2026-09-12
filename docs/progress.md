# Implementation audit

The required PLAN.md scope is complete. The final release matches all 142
tutorial verdicts and accepts init-prelude. Its 215-case arena run has 206
reference matches, four runtime declines, five configured declines, and no
wrong verdicts or errors. Both release and bounds-checking regression suites
pass. Full init is the unmet stretch target: it reaches the 600-second wall
limit. See `results.json` for all measured cases and source hashes, and
`build-performance.md` for the direct instruction profile and tradeoffs.

The evidence below includes earlier checkpoints; the completion audit at the
end records the final state.

## Implemented

- GnuCOBOL 3.2 build, with release and runtime-bounds-checking configurations.
  Each source is compiled in a separate compiler invocation, avoiding a 3.2
  cross-file compiler crash and sharing object files between test drivers.
- Arena growth by allocation/copy/free, stable 1-based handles, separate intern
  tables for names and levels, and a byte arena for name strings.
- Sparse 64-bit export indices, independent of internal handles, including
  out-of-order IDs and replacement semantics from the reference parser.
- NDJSON byte scanner with decoded UTF-8 strings, escape and surrogate validation,
  typed numeric access, metadata version checks, and name/level parsing.
- `Level.isEquiv'` and `geq'` using the reference conditional C/V sublevels and
  per-sublevel domination. Native sort comparison has a separate cached
  normal form. The complete algorithm compares its conditional normal forms
  directly; replay does not require canonical syntax reconstruction.
- Expression interning for every exported expression form, internal free
  variables, universe lists, literal blobs, and cached expression metadata.
- Binder-aware instantiation in both orders, single instantiation, abstraction
  and prefix abstraction, universe instantiation, replacement callbacks, and
  lifting; operation-local memoization preserves DAG sharing.
- Dependent-function type checking with separate checking/inference caches,
  beta/let reduction, full weak-head reduction, reducibility-hint-directed lazy
  delta, unfold and failed-argument caches, proof irrelevance, function eta,
  and union/find equivalence caching. Declaration checks have isolated caches.
- Native Lean universe normalization/equality for sort comparison, alongside
  the complete level algorithm for constant universe lists. Cached always-zero
  metadata fixes proposition detection for compound zero levels.
- Let-local inference retains dependent let bindings; lambda/let result types
  use the reference cheap beta simplification. Universe argument substitution
  and declaration type/value validation remain in place.
- Separate exported and checked environments. Dependencies are replayed before
  entering the type checker; constructors and recursors are regenerated and
  compared with exported records after replay. Unsafe/partial entries are skipped.
- Inductive validation and generation: shared parameters, universes,
  positivity, indexed return types, motives, minor premises, induction hypotheses,
  elimination levels, K flags, constructor records, and recursor types/rules.
- Nested-inductive elimination clones parser inputs, introduces auxiliary mutual
  types, validates the lowered block, restores constructors and recursors, then
  checks the nested applications in the restored environment. Auxiliary
  declarations are removed from that environment; parsed metadata is preserved.
- Recursor iota/K/structure reduction, projection typing and reduction, structure
  eta and unit-like equality. Inductive recursion flags are derived before
  constructor checking rather than taken from exported metadata. Lazy projection
  comparison and projection retries during delta reduction follow the reference.
  Inductive locals consume outParam/semiOutParam/optParam/autoParam annotations,
  which is necessary for exact recursor regeneration.
- Quotient initialization validates Eq and builds Quot, Quot.mk, Quot.lift,
  and Quot.ind; quotient eliminators reduce using those generated declarations.
- Reserved primitive names and exact Bool/Nat inductive shapes. Primitive
  definition checks cover basic arithmetic, comparisons, shifts, bitwise wrappers,
  and Char.ofNat/String.ofList entry points. Nat.mod and Nat.div additionally
  validate reflection, conditionals, and their fuel-recursive helpers.
  Nat.gcd and Nat.bitwise validate the well-founded fixpoint, recursive
  functional, fuel flow, and defining equations before native reduction is trusted.
- Nat/string literal typing and arbitrary-length Nat predecessor/constructor
  views. Decimal-limb arithmetic covers add/sub/mul/div/mod/gcd, comparisons,
  bitwise operations, shifts, powers and log2. Native Nat reduction is connected
  to weak-head and lazy-delta reduction, including the exponent guard, eager
  context and boolean shortcut. String constructor expansion decodes UTF-8
  scalars and builds String.ofList/List.{0}/Char.ofNat terms for equality,
  projection and recursor reduction. A cached has-string bit introduces the
  two implicit primitive dependencies before replaying the first string-bearing
  declaration.
- Unsupported Lean.reduceNat/Lean.reduceBool host hooks follow the reference
  rejection rule; similarly named root declarations remain ordinary constants.
- String.ofList shape checks use List.{0}, correcting an earlier universe error.
- Exit codes and resource-limit plumbing; unsupported resource demands decline.

## Current verification

- `make test` and the bounds-checking build pass: 10,859 independent level
  comparisons, 9,135 independent expression checks, malformed expression and
  declaration cases, topological replay/cycle tests, unsafe references, and
  resource-limit tests. The focused kernel suite adds 34 accept/reject cases
  for proof irrelevance, function eta, native-vs-complete universe comparisons,
  dependent lets, opaque constants, and lazy delta ordering/argument failures.
- `tests/reference-levels.sh` passes 29,418 reference-generated checks of both
  universe algorithms, including deeper max/imax DAGs.
- All 34 focused kernel cases match the pinned executable reference.
- `tests/reference-exprs.sh` passes 9,590 checks generated from the pinned
  Lean toolchain: all expression forms, cached metadata, open substitution under
  binders, both substitution orders, duplicate abstraction variables, prefix
  clamping, simultaneous universe substitution, replacement, and aliased
  single-substitution output, and cheap beta reduction.
- All 142 tutorial verdicts match the pinned executable reference: 93 accepts,
  49 rejects, no declines, mismatches, or crashes. The strict differential gate
  passes without `--allow-declines`.
- 75 additional inductive/quotient/literal regressions match the reference, including
  altered constructor metadata, recursor rule omissions/duplicates, K flags,
  ignored inductive metadata, reserved names, erased quotient headers, and
  decimal predecessor comparisons up to 5,001 digits.
  The fixtures are stored with source revision and content hashes. Mutual-block
  coverage includes parameterized tree/forest recursion, indexed even/odd
  predicates, actual mutual recursor reduction, and corrupted recursor metadata.
- All 15 currently available static/corner-case streams match the reference
  (3 accepts, 12 rejects), including `nat-rec-rules` and `rec-missing-ih`.
  There are no declines, mismatches, or crashes. This is not the complete arena run.
- 43 primitive/annotation regressions match the reference: valid primitive
  bodies, correctly typed forged bodies, extra universes, extra delta steps,
  exact recursor generation with all four type annotation gadgets, counterfeit
  deciders/conditionals/fuel helpers, and reflection proofs supplied as axioms.
  Fixtures are exported from Lean 4.33.0-rc2 and recorded with content hashes.
- `tests/reference-primitive-quotes.sh` reproduces the 78 fixed quotations
  (794 shared instructions) used by reflection validation from the pinned
  reference. The tables are compiled into COBOL; Lean is not invoked at runtime.
- 12 nested-inductive regressions match the reference and pass the bounds build.
  They cover lists, arrays, repeated/doubly nested occurrences, dependent
  parameters, indexed results, function fields and parameters, propositions,
  mutual containers, restored recursor reduction, auxiliary-recursion metadata,
  missing exports, name collisions, forbidden local indices, and hygienic names.
- The checker accepts the complete `init-prelude` stream: 63,723 records,
  7,308 interned names, 1,443 levels and 558,266 expressions after checking.
  The pinned reference also accepts it (1,774 checked declarations). A local
  release run took 11.229 seconds with 92,476 KiB maximum resident memory. Native
  arithmetic removes the former fuel exhaustion at declaration 710; correcting
  List's universe in the String.ofList primitive check resolves declaration 717.
- Nat arithmetic passes 6,890 independent Python-integer cases and 4,806 cases
  generated using the pinned Lean toolchain. Coverage includes zero division,
  saturating subtraction, carry/borrow chains, long division, GCD, bitwise/base
  conversion, large shifts, powers and resource declines. The file-based test
  driver preserves expected results longer than the console ACCEPT limit.
- The exported arithmetic fixture contains eleven definitional equalities;
  their forged-result mutations and native-hook cases exercise kernel integration.
  All 20 match the pinned reference, as do all 142 tutorial and 15 static cases.
  The full release `make test` passes, including the arithmetic oracles.
- All 41 ordinary arena cases built in this pass match the pinned reference
  (31 initial cases plus 10 built later), with no declines or errors.
- All 17 string regressions agree with the pinned reference. They cover empty
  strings, Unicode scalar/UTF-8 boundaries, embedded NUL, equality in both
  directions, projections, recursors, an 8,192-character expansion that grows
  the byte arena, forged values, escaped JSON, missing primitives, forward
  dependencies in values/binders/types, and skipped unsafe literals.
  The release `make test` passes with all 17 included, and init-prelude remains
  accepted. The full arena input build completed: 69 test definitions succeeded,
  producing 215 cases including the five configured declines.
- The complete arena run of the string/recursive release finished with 183
  correct, 15 either, 17 declined, zero wrong, and zero errors. The pinned
  reference comparison resolves all 15 either cases: 198 matching verdicts,
  12 runtime declines and five configured declines. These results precede the
  well-founded primitive changes. `tests/generated/arena-reference.json` holds
  the per-case comparison. The recursive release fix eliminates GnuCOBOL's
  deep-stack warning flood; see `build-performance.md`.
- `tests/compare-arena.py` compares saved arena verdicts against the pinned
  reference without rerunning COBOL. It requires results newer than both the
  checker binary and each input; missing/stale results and mismatches fail.
  Its first complete comparison passed on all 215 cases.
- All 31 well-founded primitive regressions match the pinned reference:
  genuine and forged GCD/bitwise definitions, extra universe parameters,
  zeta wrappers, counterfeit fixpoints, incorrect fuel, exact functional/fuel
  shape checks with ordinary-definition controls, and large GCD/land/lor/xor
  arithmetic theorems with forged-result negatives. Fixed primitive quotation
  regeneration passes with 78 quotations and 794 shared instructions.

## Earlier M0 evidence

- `make test`: 10,859 level comparisons using a separate bounded semantic
  evaluator, the five reference regressions, parser and Unicode negatives,
  interning/reallocation tests, sparse IDs, line limits, and all four exit codes.
- `tests/reference-levels.sh`: 10,857 comparisons generated by
  `Lean4Lean.Level` at bce3448115f7819fc12d647fadd3bb090666637e, including all five
  equivalence/ordering regressions in `Lean4Lean/Tests/Level.lean` and comparisons
  of all levels of size <= 5 with their reference canonical form.
- All 142 built tutorial streams and the arena checkout's 12 static NDJSON files
  scanned successfully in the bounds-checking build. These are syntax/name/level
  checks, not proof verdicts. All 154 were rescanned with the final raw-reader
  release build.
- Real arena `level-imax-normalization.ndjson` scanned: 96 records, 25 interned
  names including anonymous, 6 interned levels including zero, longest line 614.
  This is parser evidence only, not a checker verdict.

- `lka.py build-test 'init*'` produced full streams: `init-prelude` has 63,723
  records (3,714,854 bytes), longest line 2,359 bytes; `init` has 6,058,389
  records (324,561,407 bytes), longest line 3,272 bytes. The reader assembles
  64 KiB raw blocks, preserving a 4,000,000-byte per-line limit. The
  `LINE SEQUENTIAL` prototype was replaced after boundary tests exposed an
  extra EOF byte from GnuCOBOL 3.2 `LS_SPLIT` on an unterminated line exactly
  equal to the record size.
- The M0 release reader (before expression storage) scanned `init-prelude` in 0.285 seconds and `init`
  in 22.381 seconds, with the record counts above. These timings measure only
  parsing and name/level interning, not kernel checking.
- `arena/lean4cobol.yaml` and `tests/run-arena.sh` provide local registration
  and execution, with the five required large-suite declines. The wrapper
  rebuilt the current checker and ran all 142 tutorial streams through
  `lka.py`: 142 correct, with no declines, wrong verdicts, or crashes. This
  agrees with the strict direct differential against the pinned reference.
  The arithmetic build also passed the arena's init-prelude case in 10.1 seconds.

## First full init resource trial

The first arithmetic release was run under `ulimit -s unlimited`,
`ulimit -v 16000000`, and `timeout 600 perf stat -e instructions:u`. It read
all 6,058,389 records and declined (exit 2) after 131.9375 seconds; it did not
accept or finish checking the stream. Counts at exit were 278,269 names,
932 levels, and 5,873,577 expressions. The counter reported 1,065,747,136,108
user-space instructions (130.8567 seconds user, 0.4239 seconds system).
This historical trial did not enable declaration tracing and preceded the
additional limb-copy work accounting. The completed final trials below
supersede it; full init now reaches the wall-time limit.

## Completion audit

- M0: parser/exit-code plumbing, interned names and levels, both universe
  comparisons, and the normalization representations needed by the executable
  kernel are implemented and reference-tested.
- M1: expression operations and metadata are implemented and reference-tested,
  including tutorial 001–005.
- M2: dependent-function inference, weak-head reduction, lazy delta, equality,
  all cache families, delayed binder/application substitutions, and recursive
  method/loop fuel are implemented. The final bounds-checking suite passes,
  including 28 spine cases and 544 reference-generated fuel checks. See
  `typechecker-api.md` for interfaces and independent resource bounds.
- M3: inductives (including mutual/nested elimination), regenerated recursors,
  quotients, and all reserved primitive definition checks are implemented and
  have focused reference coverage.
- M4: arbitrary-precision natural arithmetic and UTF-8 string expansion are
  implemented; init-prelude was accepted at the earlier arena checkpoint.
- M5: complete. The final 215-case arena run has 191 correct, 15 either, nine
  declined, zero wrong, and zero errors. The pinned-reference comparison
  resolves all either cases: 206 matches, four runtime declines, and five
  configured declines. `results.json` and `results.csv` preserve every case.
  Init-prelude is accepted in 4.278 seconds with 66,005,820,983 instructions
  and 60,256,256 bytes peak RSS. Full init reaches the 600-second wall limit:
  the arena records 600.139 seconds, 8,847,483,839,316 instructions and
  2,817,372,160 bytes peak RSS. A separate `instructions:u` trial records
  9,399,164,836,088 instructions over 600.071 seconds. The raw direct command
  exits 124; the arena launcher translates that timeout to decline.
- M6: complete. README contains the final result table and links to the saved
  measurements, source hashes, profiling environment and implementation
  tradeoffs. Init remains an explicitly unmet stretch target.

A call-site audit of the pinned reference finds no executable replay callers
of `Level.normalize'` (canonical syntax reconstruction) or the standalone
`TypeChecker.etaExpand` utility. Those auxiliary APIs are not exposed by this
port. Kernel universe comparison and function eta equality are implemented;
this omission does not remove a replay path. The earlier list of open work
included those unused APIs provisionally, pending this audit.

Final release/arena validation and reporting are complete. The reference
checker is built locally at the required revision. See `expr-api.md` for
representation and operation interfaces.
