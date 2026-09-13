# Kernel architecture

The implementation follows lean4lean revision
`bce3448115f7819fc12d647fadd3bb090666637e`. Parsing and proof checking execute in
COBOL; GnuCOBOL compiles that source through C. The port follows the reference's
replay rules, including skipping unsafe/partial declarations.

## Storage and lifetime

Names, universe levels, expressions and lists use interned arena records with
integer handles. Hash collisions require full key comparison. Dense export IDs
use direct lookup; sparse 64-bit IDs retain hash lookup. Export IDs are mapped
to internal handles rather than used as allocation sizes.

Growing arenas call standard libc `realloc`/`free` from COBOL. New storage is
initialized in bounded chunks, and callers rebind arena views after growth.
`OCCURS UNBOUNDED` linkage views preserve subscripting in checked builds.

Successful ordinary declaration checks release temporary expression/list cells
and restore the local-ID watermark after freeing the declaration's caches.
Exported terms and generated inductive/quotient records remain persistent.
Reverse insertion-order hash deletion preserves older linear-probe chains.
Reused cells have their metadata reset. Levels remain persistent because the
universe normalization caches can retain level handles.

## Checking and caches

Dependency replay precedes declaration checking. Each declaration gets a fresh
type-checker context. Inference, reduction, definitional equality and universe
comparison follow the reference algorithms and recursive-method fuel rules.
Additional storage and structural-walk guards return resource decline.

Expression transformations memoize by the expression and relevant binding or
substitution context. Universe-parameter validation memoizes successful checks
by both immutable node and allowed parameter list. This preserves DAG sharing
without allowing a cached success under a different universe context.

Primitive equations and quotations are regenerated from the pinned reference;
the runtime checks exported primitives against kernel-owned syntax. Natural
arithmetic uses COBOL decimal limbs, with binary-limb conversion for bitwise
operations. GnuCOBOL's arithmetic runtime uses GMP internally.

## Parser and build

The byte reader preserves long lines and UTF-8 input. Canonical app/bvar/sort
records have an exact-syntax shortcut; all other syntax uses the general JSON
parser. Shortcuts match the entire record and check referenced handles before
changing state.

Bounded native-integer hashes and counter arithmetic reduce decimal conversion
costs. Release builds use `scripts/prepare-cobol.py` to give nonrecursive helpers
secondary public `ENTRY` declarations, avoiding GnuCOBOL's primary-entry stack
walk. Procedure bodies are copied verbatim; recursive procedures are unchanged.
Debug builds compile the original entry declarations with runtime checks.

Each source is compiled separately. Build modes have separate objects and
executables, and compiler/flag changes invalidate the affected mode. The Nix
toolchain is pinned in `flake.lock`.

Detailed interfaces: [expressions](expr-api.md), [type checking](typechecker-api.md),
[natural arithmetic](nat-api.md), and [strings](string-api.md).
