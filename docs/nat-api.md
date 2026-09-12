# Natural arithmetic

`bignum-calc(state, operation, lhsBlob, rhsBlob, resultBlob)` consumes canonical
nonnegative decimal blobs and interns its canonical decimal result. The kernel
parser enforces canonical input. Comparison results are decimal zero or one.
The operation codes are:

| Codes | Operations |
| --- | --- |
| 1–3 | add, saturating sub, mul |
| 4–6 | div, mod, gcd |
| 7–8 | beq, ble |
| 9–11 | land, lor, xor |
| 12–15 | shiftLeft, shiftRight, pow, log2 |

Eight scratch registers use little-endian binary 32-bit limbs in base 10^9.
Products and carries use 64-bit intermediates. Multiplication is schoolbook;
division uses a single-limb fast path or long division with an exact quotient
digit search. GCD iterates remainders. Bitwise operations convert to 30-bit
binary limbs and back. Powers use repeated squaring. Shifts use multiplication
or division by powers of two of at most 29 bits.

A conservative capacity estimate above one million limbs or more than twenty
million arithmetic limb operations declines (exit 2). Scratch storage is freed
on every post-allocation exit. The test driver also exercises allocation growth
and expected results exceeding the console's ACCEPT limit.

`reduce-nat(state, expr, depth, result)` returns zero when ineligible and an
expression handle when reduced. It follows TypeChecker.reduceNat: unary
Nat.succ requires an empty universe list; binary operations match by name and
exact arity, reduce operands with whnf, and recognize only raw Nat literals or
Nat.zero with an empty universe list. Pow declines native reduction when its
exponent exceeds 2^24, allowing ordinary definition reduction to proceed.
Log2 is an arithmetic API operation, not an added kernel native reduction.

Full whnf calls reduce-native then reduce-nat before delta unfolding. Lazy
delta only tries Nat reduction when both operands are closed or the eager
context is set. Argument checking sets and restores that context for an
application of eagerReduce with two arguments. The closed/eager Bool.true
shortcut precedes proof-irrelevance inference as in the reference.

`reduce-native` rejects exactly Lean.reduceBool/Lean.reduceNat with empty
universe lists applied to a constant. It executes no host code. Root names
reduceBool/reduceNat and applications with extra universes do not match.

`tests/test_nat.py` uses Python's integers as an independent oracle;
`tests/reference-nats.sh` generates cases from Nat operations in the pinned Lean
toolchain. Exported equalities and their forged-result mutations live in
`tests/test_arithmetic.py`. Tests and fixture generation use Python/Lean; the
runtime checker uses only COBOL.
