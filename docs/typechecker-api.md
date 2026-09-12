# Type checker interfaces and fidelity notes

All calls take `kernel-state` by reference. Expression and level arguments are
interned handles; expression handle zero is a missing result, while level handle
one is zero. Programs preserve the first nonzero `verdict`. Depth arguments are
unsigned 32-bit integers; equality answers are unsigned bytes (0 false, 1 true).
`def-quick` and `lazy-delta` also return 2 for undecided.
`lazy-delta-step` additionally returns 3 to continue with the reduced pair.

- `infer-type(state, expr, depth, result)` checks by default. The internal
  `tc-infer-only` mode selects its separate inference-only cache.
- `infer-only(state, expr, depth, result)` temporarily selects inference-only
  mode. As in the reference, callers must already know the term is well typed.
- `infer-sort(state, expr, depth, level)` infers then ensures a sort.
- `weak-head-core(state, expr, depth, result)` reduces beta/let/metadata/local
  lets, without delta unfolding. `weak-head-cheap` suppresses cache writes;
  its projection hook reduces the structure only with core reduction. Both can read the normal core cache.
- `weak-head(state, expr, depth, result)` additionally unfolds definition and
  theorem heads. Opaque declarations do not unfold. `delta-info` and
  `unfold-head` require exactly the declared number of universe arguments.
- `def-equal(state, lhs, rhs, depth, answer)` adds successful equalities to the
  equivalence manager. `def-equal-core` has the same interface without that
  final insertion. Both assume well-typed inputs.
- `expr-cheap-beta(state, expr, result)` is the closed-expression helper from
  `Lean4Lean/Instantiate.lean`: it reduces a lambda application only when the
  residual body is closed or selects a supplied argument, preserving leftover
  applications. It performs no general substitution or delta unfolding.
- `level-native-equal(state, lhs, rhs, answer)` ports native `Level.isEquiv` for
  quick sort comparison. It deliberately differs from `level-compare` mode 0,
  the complete `isEquiv'` used for constant universe lists. The native normal
  form uses a stable internal handle order; it is not an export of Lean's
  lexicographically ordered normal-form syntax.

`check-declaration` starts a fresh `tc-context` and restores its caller on every
exit, including failures. Dependency replay now happens before type checking;
`name-decl` maps to exported records and `name-env` to checked/generated records. Local identifiers remain
unique for the whole stream. All context cache storage is released when its
check finishes. Families in `tc-cache` are:

| Family | Contents |
| --- | --- |
| 1 | Checked type inference |
| 2 | Inference on known well-typed expressions |
| 3 | Core weak-head normalization |
| 4 | Full weak-head normalization |
| 5 | Universe-instantiated unfolded constant bodies |
| 6 | Failed same-definition argument comparisons |
| 7 | Equivalence union/find parents |
| 8 | Equivalence union/find ranks |

Structural equivalence observes the reference's hash gate and recursively uses
known equivalences. After the hash gate it ignores projection type names and let
nondependency flags, matching `EquivManager.lean`. Interning itself retains those
fields. Successful pairs merge by rank; lookups compress paths. Pair-failure
keys use sorted stable handles instead of expression hashes.

Lazy delta compares reducibility hints (opaque < regular < abbrev), breaking
regular ties by height. For applications of the same regular definition it first
compares arguments from last to first, remembering failure before unfolding.
Final application congruence compares equal-length spines from first to last.
Proof irrelevance precedes delta; function eta follows application congruence.
When only one head can unfold, the other side first retries projection reduction.
Matching projections use `lazy-delta-projection`: compare structures by lazy
unfolding, then compare their selected fields when unfolding stalls.

Primitive defining equations compare candidate bodies before installing their
names in the environment. `primitive-template` builds kernel-owned quoted terms
in postfix notation; it never interprets export content. Reflection and
condition checks for Nat.mod/Nat.div use fixed quotations regenerated from
`tests/primitive-quotes.lean`. `reflection-quote` interprets compiled expression
instructions with holes supplied by the validation context. It uses a fresh
local memo table for each quotation and never reads executable input text.
Nat.gcd/Nat.bitwise validate the well-founded fixpoint shape, fuel flow and
recursive equations; focused mutations have reference-verdict coverage.
Set `LEAN4COBOL_TRACE=1` to report
which exported declaration or primitive equation first fails.

String constructors and literal equality are described in `string-api.md`.
Nat arithmetic, native-hook rejection and eager reduction are described in
`nat-api.md`.

Consecutive lambda, forall and let binders delay substitution until the end of
that group. Domains are instantiated against the already-open locals. Lambda
and forall equality use the same delayed substitution strategy. Inference-only
applications consume raw forall prefixes before substituting their arguments;
core beta reduction consumes a syntactic lambda prefix in one substitution and
then reapplies unused arguments. These paths have 28 focused reference cases.

`tc-methods.cob` implements `Methods.withFuel`: the four recursive method entry
points consume a depth unit, including cache hits, and restore that unit on
return or failure. Direct calls to the reference's primed implementations keep
the current method budget. The defaults in `FuelConfig.lean` are stored separately
from the structural recursion guard: 50,000 method depth, 100,000 ordinary whnf
iterations, 1,000,000 eager iterations, and 1,000 lazy-delta/inductive iterations.
The former aggregate million-operation cap has been removed. 544 generated
checks compare small method budgets, cache hits, direct calls, and ordinary/eager
loop boundaries against the reference. Expression transformations, level
normalization, bignum work and arena sizes retain independent resource bounds.
Fuel or resource exhaustion always declines.

Inductive packages regenerate their constructors/recursors; postponed exported
records are then compared exactly. `nested-lower` clones parsed records and
replaces nested applications with auxiliary mutual types. `nested-restore`
restores constructor types, recursor types and rules, and maps auxiliary
recursors to public names. It retains the temporary environment until every
expression has been restored, then installs only the public declarations and
checks the original nested applications with fresh type-checker caches.
Temporary parser bindings are restored on success and failure.
Quotient headers are treated as initialization requests as in the reference
importer.
