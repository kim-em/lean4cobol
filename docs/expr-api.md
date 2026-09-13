# Expression representation and operations

`src/copy/expr.cpy` describes the interned expression nodes. Kind tags are:

| Kind | A | B | C | D |
|---|---|---|---|---|
| 0 bvar | index | 0 | 0 | 0 |
| 1 sort | level | 0 | 0 | 0 |
| 2 const | name | universe list | 0 | 0 |
| 3 app | function | argument | 0 | 0 |
| 4 lam / 5 forall | domain | body | 0 | 0 |
| 6 let | type | value | body | nondep |
| 7 proj | structure name | field index | structure expression | 0 |
| 8 nat / 9 string | literal blob | 0 | 0 | 0 |
| 10 fvar | fresh local ID | 0 | 0 | 0 |
| 11 mdata | expression | 0 | 0 | 0 |

Binder names and binder annotations do not affect Lean's `Expr.eqv`, so the
interner discards them. The `let` dependency flag does affect equality. Exported
metadata is represented by an empty metadata wrapper, matching lean4export's
parser. All handles are immutable and 1-based; zero is null, including an empty
handle list. Naturals use canonical decimal blobs at the expression boundary and decimal
limbs during arithmetic; see `nat-api.md`.

The interner computes the hash, loose-bound-variable range, and the free-variable
and level-parameter flags once. `expr-eqv` compares handles; `expr-data` returns
the cached metadata. A has-string-literal bit is also propagated through all
expression children for implicit replay dependencies. `hasLooseBVars` is `loose-range > 0`. Hashes implement this
port's multiply-add scheme, not Lean's numeric hash function.

`expr-ops.cob` exposes `expr-instantiate`, `expr-instantiate-rev`,
`expr-instantiate1`, `expr-abstract`, `expr-abstract-range`, `expr-level-params`,
`expr-lift`, and `expr-replace`. General vectors are contiguous `(key, value)`
pairs of unsigned binary-long items; pass their pointer and count. Instantiation
and abstraction use only the value. Level instantiation uses name keys and level
values; callers zip the lists up to the shorter length. `expr-abstract-range`
clamps its prefix length to the vector length. Single instantiation supports an
aliased input/output handle.

Replacement callbacks receive `(kernel-state, context-pointer, input-handle,
output-handle)`. Output zero requests descent; a nonzero output replaces the
whole node without visiting its children. Each operation owns a memo table keyed
by expression and binding depth, released on return. Replacement and universe
substitution cache independently of binder depth. Universe substitution uses
Lean's cheap `mkLevelMax'`/`mkLevelIMax'` rebuilding rules.

Callers must pass valid arena handles and distinct argument/output variables to
interning routines. Internal subprograms share `kernel-state.verdict`; after an
error, calls propagate it without further semantic work. Resource exhaustion is
2 (decline). Recursive calls use local storage, and the arena launcher gives the
process an unlimited stack.
