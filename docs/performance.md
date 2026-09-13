# Performance and validation

Both checkers accept the same exported Init and Mathlib inputs with no
wall-clock timeout and an unlimited stack.

| Input | lean4cobol | lean4lean | COBOL peak RSS |
| --- | ---: | ---: | ---: |
| Init | 728.415 s | 58.096 s | 492.20 MiB |
| Mathlib | 15,576.516 s | 4,247.795 s | 7.09 GiB |

Mathlib took **4 h 19 m 37 s**, compared with **1 h 10 m 48 s** for lean4lean:
3.67 times the wall time and 9.20 times the user-space instructions.
COBOL executed 129,625,380,995,922 instructions, with 15,301.423 seconds of user
CPU time and 174.475 seconds of system CPU time. Lean4lean executed
14,087,678,816,219 instructions, with 3,562.328 seconds of user CPU time and
454.663 seconds of system CPU time.

The host is a shared AMD EPYC 9455 machine running Linux 6.12.100, with 96 logical
CPUs. The reference experienced substantial swapping; memory pressure eased
before the COBOL run. Wall-time ratios are not isolated performance comparisons.

Mathlib v4.29.1 (`5e932f97dd25535344f80f9dd8da3aab83df0fe6`) produced a
5,636,308,621-byte export with 100,001,405 records and 670,630 exported
declarations. Lean4lean reports 654,501 checked declarations. Exported records
and checked declarations are different counts; both processes accepted the
complete file. The reference is pinned to
`bce3448115f7819fc12d647fadd3bb090666637e`, using Lean v4.33.0-rc2.

[benchmarks.json](benchmarks.json) records the exact measured source and binary
hashes, input hashes, CPU times and instruction counts. Build packaging changes
do not replace the measured kernel revision or imply a new Mathlib measurement.

## Runtime costs

Profiles show substantial GnuCOBOL allocation, field conversion and decimal
arithmetic costs. A 15-second Mathlib parsing sample attributed 10.3% of user
CPU samples to `calloc` and 7.5% to `cob_move`, with further costs in decimal
conversion and GMP. This is a phase sample, not a whole-run attribution.

The implementation uses native-integer hashing, dense export-ID lookup,
declaration-local reclamation, exact-syntax parser shortcuts and memoized
universe validation. The [architecture](architecture.md) describes their
invariants and the release helper-entry transformation.

## Coverage

All **211 measured arena inputs** agree with lean4lean: 209 arena runner
results, plus the direct Init and Mathlib measurements. All 25 performance cases
return their expected verdicts. Performance runs used a 48 GiB virtual-memory
ceiling; the direct Init and Mathlib runs did not. None used a wall timeout.
[Case results](results.json) and the [CSV table](results.csv) record measurements.

Release and checked regression suites pass. Coverage includes 20,032 hash
oracle cases, 216 fast/general parser comparisons, 36 focused kernel cases,
9,590 reference expression cases, 29,418 universe comparisons, and a 2.68 GB
arena/reclamation check. Shared-DAG regressions test both acceptance with valid
universe parameters and rejection under a different parameter list.
