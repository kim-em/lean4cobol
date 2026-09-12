# Unlimited Mathlib run and performance work

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
  COBOL. The recorded wall times therefore include substantial shared-host
  memory contention.

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

## Final Init measurement

The final build accepted Init in **797.669 seconds** (13 minutes 18 seconds),
with **5,194,666,037,130 instructions** and **490,224 KiB peak RSS**. Compared
with the pinned reference’s 58.096 seconds and 519,949,070,210 instructions,
this is about 13.7 times the elapsed time and 10.0 times the instruction count.
Compared with the first fully accepting intermediate COBOL build, the final
build uses about 68.5% fewer instructions. The shared host affects elapsed-time
ratios; these are observed whole-process measurements.

The remaining profile shows substantial GnuCOBOL call-frame/local-storage
allocation and decimal-arithmetic overhead. The port retains the reference’s
checking algorithms and fuel behavior; further reductions would require more
substantial changes to its COBOL execution structure.

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
comparisons generated by lean4lean pass. All 209 non-declined arena cases other than Init/Mathlib agree with the
pinned reference; four other libraries are explicitly declined. All 25 arena
performance cases accept, including the three previously stopped by expression
limits. The [case-level results](arena-unlimited-results.json) and
[CSV table](arena-unlimited-results.csv) contain the measurements. Mathlib's
final result and the submission revision will be recorded when the large runs
complete.

After committing the validated source, prepare the exact upstream entry with:

```sh
python3 scripts/prepare-arena-submission.py --revision HEAD
```

This produces a pinned YAML entry, an arena patch and a draft PR body under
`_tmp/arena-submission/`. The destination is
`leanprover/lean-kernel-arena` (default branch `master`). Publishing the source
commit and submitting that patch are separate from preparing these files.
