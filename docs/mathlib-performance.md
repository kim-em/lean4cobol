# Unlimited Mathlib run and performance work

**Mathlib accepted in 4 hours 19 minutes 37 seconds**, with 7.09 GiB peak
resident memory. The pinned lean4lean reference accepted the same export in
1 hour 10 minutes 48 seconds. The COBOL run took 3.67 times the wall time and
9.20 times the user-space instructions. Both ran without a wall-clock timeout.

This is the follow-up to the historical, time-limited measurements in
`results.json`. Those measurements describe an earlier executable.

The current launcher has no wall-clock timeout. `LEAN4COBOL_PROGRESS=1`
reports parsing and replay progress; `LEAN4COBOL_TRACE=1` identifies a failing
declaration. A successful `--scan` is parsing only, not proof checking.

## Inputs and reference

- Arena Mathlib release: v4.29.1, commit
  `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
- Export: `_tmp/arena/_build/tests/mathlib.ndjson`, 5,636,308,621 bytes and
  100,001,405 records, produced with the arena’s `build-test mathlib` command.
- lean4lean reference: `bce3448115f7819fc12d647fadd3bb090666637e`, built with
  its pinned Lean v4.33.0-rc2 toolchain.
- Runs use the same exported file and unlimited stack. The machine is shared;
  elapsed times are observations, while instruction counts help distinguish
  implementation changes from host load. During Mathlib replay, `/proc`
  showed approximately 7.4 GiB swapped out for the reference and 5.4 GiB for
  the superseded COBOL build. Pressure eased before the completed memoized
  run. These wall times are not an isolated or equally loaded comparison.

## Completed baseline

The original COBOL implementation, with the external timeout removed, took
832.395 seconds on Init and declined at 33,554,432 expression nodes, at exported
declaration 33,753. It executed 13,238,617,029,614 user-space instructions.
The reference accepted Init’s 53,090 checked declarations in 58.096 seconds
and 519,949,070,210 user-space instructions.

A paired Init-prelude trial used the original and revised executables in
sequence. Both accepted. The original took 6.619 seconds and
65,874,188,604 instructions; the revised implementation with native hashing
and secondary helper entries took 2.387 seconds and 27,720,386,074 instructions.
Peak memory in separate trials fell from approximately 60 MB to 21 MB.
These prelude measurements are not a claim about full Mathlib performance.

The first revised implementation accepted Init in 1,396.571 seconds using
16,500,257,879,955 instructions and 732,656 KiB peak RSS. This intermediate
variant used temporary-node reclamation and larger arenas but preceded the
native-hash/helper-entry optimizations. Its successful result establishes that
the original expression cap was a storage issue, not a rejected proof.

## Init measurement before validation memoization

The pre-memoization build accepted Init in **797.669 seconds** (13 minutes 18 seconds),
with **5,194,666,037,130 instructions** and **490,224 KiB peak RSS**. Compared
with the pinned reference’s 58.096 seconds and 519,949,070,210 instructions,
this is about 13.7 times the elapsed time and 10.0 times the instruction count.
Compared with the first fully accepting intermediate COBOL build, this
build uses about 68.5% fewer instructions. The shared host affects elapsed-time
ratios; these are observed whole-process measurements.

The remaining profile shows substantial GnuCOBOL call-frame/local-storage
allocation and decimal-arithmetic overhead. The port retains the reference’s
checking algorithms and fuel behavior; further reductions would require more
substantial changes to its COBOL execution structure.

## Current Init measurement

With validation memoization, Init accepts in **728.415 seconds** (12 minutes
8 seconds), executing **4,939,477,247,833 instructions**, with **504,012 KiB
peak RSS**. This is 12.5 times the reference wall time and 9.5 times its
instruction count. The instruction count is 70.1% below the first accepting
COBOL intermediate, and 4.9% below the pre-memoization build.

## Completed Mathlib measurements

The pinned lean4lean reference accepted all **654,501 checked declarations** in
**4,247.795 seconds** (1 hour 10 minutes 48 seconds), with
**14,087,678,816,219 user-space instructions**. CPU time was 3,562.328 seconds
in user space and 454.663 seconds in the kernel.

The memoized COBOL build accepted the complete export in **15,576.516 seconds**
(4 hours 19 minutes 37 seconds), with **129,625,380,995,922 user-space
instructions** and **7,431,760 KiB peak RSS**. CPU time was 15,301.423 seconds
in user space and 174.475 seconds in the kernel. It processed all 100,001,405
records and 670,630 exported declarations, finishing with 105,127,374 expression
nodes. The process returned exit code 0 and printed `accepted`.

The different declaration counts distinguish exported records from the
reference's checked declarations. Both checkers accepted the identical file.
The exact source revision, hashes and measurements are in
[unlimited-results.json](unlimited-results.json).

## Shared-DAG validation bottleneck

A subsequent profile of a stalled Mathlib declaration identified repeated
universe-parameter validation. That pass traversed shared expression DAGs as
expanded trees. Successful expression and level checks are now memoized by
both node and allowed parameter list, within the existing declaration-local
cache. Failures are never cached as successes.

An 18-level shared-DAG test dropped from 1,989,908,925 to 11,855,699
instructions (about 168 times fewer). A 35-level case, representing more than
34 billion tree leaves, passes and agrees with lean4lean; omitting its allowed
universe is still rejected. Init and Mathlib both completed with this correction.
The earlier Mathlib trial was stopped as a superseded variant, not recorded
as a completed check.

A 15-second sample during parsing of the memoized Mathlib run still attributes
10.3% of user CPU samples to `calloc`, 7.5% to `cob_move`, and substantial
additional time to GnuCOBOL field/decimal conversion and GMP arithmetic. This
is a parsing-phase sample, not a whole-run attribution. It explains why the
remaining cost cannot be inferred solely from the proof-checking algorithm.

## Changes and why checking remains faithful

- Ordinary declaration checks discard temporary expression/list cells and
  local variables after freeing their type-checker caches. Exported terms and
  generated inductive/quotient declarations remain persistent. Hash entries
  are removed in reverse insertion order, preserving older probe chains.
- Larger arenas use standard libc `realloc`/`free` storage calls from COBOL,
  bypassing GnuCOBOL 3.2’s allocation cap. COBOL initializes the new region in
  bounded chunks. `OCCURS UNBOUNDED` views retain runtime subscripting in
  checked builds. No proof-checking code is implemented in C.
- Consecutive export IDs use compact direct lookup tables. Sparse 64-bit IDs
  retain hash lookup, including sparse entries subsequently covered by an
  expanding direct table.
- Exact canonical app/bvar/sort records have a parser shortcut. The entire
  record must match before state changes; other syntax uses the general
  parser. Referenced handles are still checked.
- Expression, list and type-checker hashes use bounded machine-integer
  arithmetic. The mixing polynomial is modulo `2^31-1`; Schrage decomposition
  keeps every signed intermediate in range. Hash matches still require full
  key comparison. Hash values are representation details, not proof evidence.
- Linear-probe wrapping, metadata maxima and simple counter arithmetic avoid
  GnuCOBOL decimal intrinsics.
- Release builds give nonrecursive helper programs secondary public `ENTRY`
  points. GnuCOBOL 3.2 otherwise either scans the whole call stack or allocates
  recursive module/frame/decimal state for each helper call. The preparation
  script copies procedure bodies verbatim. Recursive procedures are unchanged;
  `make debug` compiles original entries with runtime recursion checks.

## Validation and submission

The final release and checked regression suites pass, including the 2.68 GB
arena/reclamation test, 20,032 independent hash checks and 216 fast/general
parser comparisons. A further 9,590 expression cases and 29,418 universe
comparisons generated by lean4lean pass. The 36 focused kernel cases, including
the shared-DAG regressions, agree with the reference. All **211 non-declined
arena inputs** agree with the pinned reference; four other libraries are
explicitly declined. This combines 209 official arena runner results with the
direct Init/Mathlib measurements. All 25 arena performance cases return their
expected verdicts, including acceptance of the three previously stopped by
expression limits. The [case-level results](arena-unlimited-results.json) and
[CSV table](arena-unlimited-results.csv) contain the measurements. Performance
reference verdicts were reused from the prior comparison on the same unchanged
exports; the current COBOL performance results were rerun. Performance runs
inherited a 48 GiB virtual-memory ceiling; the direct Init and Mathlib runs did
not. None used a wall-clock timeout.

After committing the validated source, prepare the exact upstream entry with:

```sh
python3 scripts/prepare-arena-submission.py --revision HEAD
```

This produces a pinned YAML entry, an arena patch and a draft PR body under
`_tmp/arena-submission/`. The destination is
`leanprover/lean-kernel-arena` (default branch `master`). Publishing the source
commit and submitting that patch are separate from preparing these files.
