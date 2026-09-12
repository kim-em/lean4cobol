import Lean4Lean.TypeChecker

/- Fixed-field oracle for tests/nat-driver.cob. These are the native Nat
operations called by TypeChecker.reduceNat at the pinned reference revision. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def emit (op a b result : Nat) : IO Unit :=
  IO.println s!"{op} {a} {b} {result}"

private def pair (a b : Nat) : IO Unit := do
  emit 1 a b (a + b)
  emit 2 a b (a - b)
  emit 3 a b (a * b)
  emit 4 a b (a / b)
  emit 5 a b (a % b)
  emit 6 a b (Nat.gcd a b)
  emit 7 a b (if a == b then 1 else 0)
  emit 8 a b (if a <= b then 1 else 0)
  emit 9 a b (Nat.land a b)
  emit 10 a b (Nat.lor a b)
  emit 11 a b (Nat.xor a b)

private def next (state : Nat) : Nat :=
  (state * 6364136223846793005 + 1442695040888963407) % (2^64)

private def randomNat (size : Nat) (state : Nat) : Nat × Nat := Id.run do
  let mut s := state
  let mut value := 0
  for _ in [:size] do
    s := next s
    value := value * 2^64 + s
  return (value, s)

def main : IO Unit := do
  let edge := #[0, 1, 2, 10^9-1, 10^9, 10^9+1, 2^30-1, 2^30,
    2^64-1, 2^64, 10^18-1, 10^18, 10^18+1, 10^45-1, 10^45, 10^45+1, 2^256-1]
  for a in edge do
    for b in edge do pair a b
    for b in #[0, 1, 2, 28, 29, 30, 31, 59, 60, 61, 255, 1000] do
      emit 12 a b (Nat.shiftLeft a b)
      emit 13 a b (Nat.shiftRight a b)
    for b in #[0, 1, 2, 3, 10, 31] do emit 14 a b (a^b)
    emit 15 a 0 (Nat.log2 a)
  let mut state := 904172
  for i in [:100] do
    let (a, s) := randomNat (i % 20 + 1) state
    let (b, s) := randomNat ((i * 13) % 24 + 1) s
    state := s
    pair a b
