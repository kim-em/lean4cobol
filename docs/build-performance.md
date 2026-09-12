# GnuCOBOL build behavior

Each COBOL source is compiled in a separate compiler process. With GnuCOBOL 3.2,
compiling several complex modules in one invocation reproducibly crashed the
compiler on the module after a variable-length local table. Shared object files
also let all test drivers reuse the compiled kernel.

Release builds pass `-fno-recursive-check`; the debug target retains GnuCOBOL's
recursion checks. This flag treats helpers as recursive programs, without changing
the COBOL kernel's own depth/fuel limits or proof checks. The kernel passes its
mutable state explicitly and uses local storage for invocation state.

The first full arena run exposed why this matters. On perf/app-lam, a 3-second
sample attributed 60.64% of cycles to cob_get_source_line and 32.20% to
cob_module_global_enter. GnuCOBOL 3.2's libcob/common.c scans the active module
chain on entry to an already-initialized nonrecursive program. At more than
10,240 modules it emits a warning, and source-location lookup scans the chain
again. Deep but valid kernel recursion repeatedly calling small helpers
therefore generated 394,353,462 bytes of warnings and timed out after 600 seconds.

The compiler's cobc/tree.c implements -fno-recursive-check by marking each
program recursive. The generated code then allocates a module record for each
invocation, avoiding the nonrecursive-entry scan. No runtime library patch or
foreign-language checker code is used. The release regression suite passes with
this setting. The perf/app-lam rerun returned decline (exit 2) after 221.436
seconds, at 33,554,432 interned expressions, instead of timing out. Its instruction
count was 2,018,026,139,211. A second sample no longer showed the module-stack
scans among the hot functions; decimal conversions and allocation dominated.
The test still exceeds the expression-arena resource bound, so this is a runtime
fix, not acceptance of the performance test.

The exact runtime source used for this investigation can be obtained with:

```sh
nix build nixpkgs#gnucobol.src --no-link --print-out-paths
```

This resolved to the GnuCOBOL 3.2 source archive in the implementation environment.

## Data representation tradeoffs

Integer handles make expression identity, DAG sharing and memo-table keys
straightforward. GnuCOBOL's binary storage and explicit ALLOCATE/FREE operations
are sufficient for growing arenas without allocating a separate object for each
expression. Rebinding every arena view after allocation is essential: a stale
BASED view can otherwise refer to freed storage.

Decimal limbs suit native COBOL arithmetic and decimal literal parsing. Division
and GCD can stay in base 10^9; bitwise operations convert through 30-bit binary
limbs. The bignum module makes no direct foreign-library calls, at the cost of
conversion work for large bitwise operations. GnuCOBOL itself uses GMP inside
its arithmetic runtime.

Interned expressions remain in their arenas for the whole stream. Declaration
caches are released after each check, but intermediate expression nodes are not
garbage-collected. Stable handles and simple allocation come at the cost of
retaining those intermediates; the large application and magma cases can reach
the 33,554,432-expression arena bound.

Local storage permits direct recursive kernel routines, but large recursive
frames and the C stack still matter. Grouped binder/application substitution
reduces repeated expression rebuilding. Resource guards protect structural
walks, bignum work, arenas and input size independently of the reference's
recursive-method fuel. The arena launcher also bounds virtual memory and wall
time; timeout status 124 is translated to decline, while other abnormal exits
remain errors.

The raw-block reader avoids the line-sequential runtime's boundary behavior and
handles long Unicode-bearing NDJSON records byte-for-byte. Fixed compiled
quotations make primitive checks reviewable: the runtime fills expression holes
in trusted kernel-owned syntax instead of parsing or evaluating program text
from an export. The Lean and Python tools used to generate fixtures are test
dependencies; they are not part of checking a stream.

A 3-second sample during the final init run (299 samples, no lost samples)
again showed allocation and arithmetic conversion costs rather than module
stack scans: 8.45% in calloc, 7.75% in cob_decimal_set_field, 4.73% in
_int_malloc, and 3.37% in cob_decimal_get_field. Runtime GMP operations also
appear among the hot functions. This is a short diagnostic sample, not a
whole-run profile or a comparison of checker algorithms.

## Final measurement environment

The final run uses x86_64 Linux 6.12.100 on an AMD EPYC 9455 48-Core
Processor host (96 logical CPUs), with GnuCOBOL 3.2.0 and the release flags in
Makefile. It is a shared host, so wall times are observations rather than
controlled performance comparisons. Arena measurements include its launcher
and timing wrappers.

The direct user-space instruction profile is run with the timeout inside perf,
so the profiler can emit its counters even when the checker reaches the limit:

```sh
ulimit -s unlimited
ulimit -v 16000000
perf stat -e instructions:u timeout 600 bin/lean4cobol init.ndjson
```

Putting timeout outside perf terminated the profiler before it emitted counters
in the first final trial; that trial is not used for the direct instruction
count. The arena independently recorded its full 600-second init trial.

The completed direct trial recorded 9,399,164,836,088 user-space instructions
in 600.070578633 seconds (597.179760000 user, 1.032536000 system), then
exited 124 at the timeout. The separate arena trial recorded
8,847,483,839,316 instructions in 600.138982807 seconds and a peak resident
size of 2,817,372,160 bytes; its launcher returned decline (2). These are
separate time-bounded trials, so they can complete different amounts of work.
Neither accepted init.
