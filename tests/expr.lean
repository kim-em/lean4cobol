import Lean
import Lean4Lean.Instantiate

/- Fixed-field Expr operation cases emitted by Lean, consumed by expr-driver.cob.
   All verdicts/expected expressions come from Lean's executable Expr APIs. -/
open Lean

private structure EmitState where
  names : Std.HashMap Name Nat := {}
  levels : Std.HashMap Level Nat := { (.zero, 0) }
  lists : Std.HashMap (List Level) Nat := { ([], 0) }
  exprs : Std.HashMap Expr Nat := {}
  literals : Std.HashMap String Nat := {}
  nextExpr : Nat := 1
  checks : Nat := 0

private abbrev M := StateT EmitState IO

private def nameId (n : Name) : M Nat := do
  if let some id := (← get).names[n]? then return id
  let id := (← get).names.size + 1
  modify fun s => { s with names := s.names.insert n id }
  return id

private def emitLevel (l : Level) : M Nat := do
  if let some id := (← get).levels[l]? then return id
  let (k, a, b) ← match l with
    | .zero => pure (0, 0, 0)
    | .succ a => do pure (1, ← emitLevel a, 0)
    | .max a b => do pure (2, ← emitLevel a, ← emitLevel b)
    | .imax a b => do pure (3, ← emitLevel a, ← emitLevel b)
    | .param n => do pure (4, ← nameId n, 0)
    | .mvar _ => throw <| IO.userError "unexpected level metavariable"
  let id := (← get).levels.size
  modify fun s => { s with levels := s.levels.insert l id }
  IO.println s!"L {id} {k} {a} {b} 0 0"
  return id

private def emitList (ls : List Level) : M Nat := do
  if let some id := (← get).lists[ls]? then return id
  let h :: t := ls | return 0
  let a ← emitLevel h
  let b ← emitList t
  let id := (← get).lists.size
  modify fun s => { s with lists := s.lists.insert ls id }
  IO.println s!"S {id} {a} {b} 0 0 0"
  return id

private def literalId (l : Literal) : M Nat := do
  let key := reprStr l
  if let some id := (← get).literals[key]? then return id
  let id := (← get).literals.size + 1
  modify fun s => { s with literals := s.literals.insert key id }
  return id

private def emit (e : Expr) : M Nat := do
  if let some id := (← get).exprs[e]? then return id
  let (k, a, b, c, d) ← match e with
    | .bvar n => pure (0, n, 0, 0, 0)
    | .sort u => do pure (1, ← emitLevel u, 0, 0, 0)
    | .const n us => do pure (2, ← nameId n, ← emitList us, 0, 0)
    | .app f a => do pure (3, ← emit f, ← emit a, 0, 0)
    | .lam _ d b _ => do pure (4, ← emit d, ← emit b, 0, 0)
    | .forallE _ d b _ => do pure (5, ← emit d, ← emit b, 0, 0)
    | .letE _ t v b nd => do pure (6, ← emit t, ← emit v, ← emit b, if nd then 1 else 0)
    | .proj n i e => do pure (7, ← nameId n, i, ← emit e, 0)
    | .lit l@(.natVal _) => do pure (8, ← literalId l, 0, 0, 0)
    | .lit l@(.strVal _) => do pure (9, ← literalId l, 0, 0, 0)
    | .fvar ⟨n⟩ => do pure (10, ← nameId n, 0, 0, 0)
    | .mdata _ e => do pure (11, ← emit e, 0, 0, 0)
    | .mvar _ => throw <| IO.userError "unexpected expression metavariable"
  let id := (← get).nextExpr
  modify fun s => { s with exprs := s.exprs.insert e id, nextExpr := id + 1, checks := s.checks + 1 }
  IO.println s!"E {id} {k} {a} {b} {c} {d}"
  IO.println s!"D {(← get).checks} {id} {e.looseBVarRange} {if e.hasFVar then 1 else 0} {if e.hasLevelParam then 1 else 0} 0"
  return id

private def operation (mode : Nat) (e expected : Expr) (pairs : Array (Nat × Nat))
    (amount : Nat := 0) : M Unit := do
  let input ← emit e
  let want ← emit expected
  let id := (← get).nextExpr
  modify fun s => { s with nextExpr := id + 1, checks := s.checks + 1 }
  let vector := String.intercalate " " <| pairs.toList.map fun (k,v) => s!"{k} {v}"
  IO.println s!"T {id} {mode} {input} {amount} {pairs.size} 0 {vector}"
  IO.println s!"C {(← get).checks} {id} {want} 0 0 0"

private def u : Level := .param `u
private def v : Level := .param `v
private def f (n : Name) : Expr := .fvar ⟨n⟩
private def atoms : Array Expr := #[.bvar 0, .bvar 1, .bvar 2, .bvar 3, .bvar 4,
  f `x, f `y, f `z, .sort .zero, .sort u, .sort (.imax u (.max v (.succ u))),
  .const `c [u, v, .zero], .lit (.natVal 123456789012345678901234567890),
  .lit (.strVal "hé😀")]

private def advance (n : Nat) := (n * 1664525 + 1013904223) % 4294967296

private def samples : Array Expr := Id.run do
  let mut seed := 57891
  let mut pool := atoms
  for _ in [:700] do
    seed := advance seed
    let kind := seed % 6
    seed := advance seed
    let a := pool[seed % pool.size]!
    seed := advance seed
    let b := atoms[seed % atoms.size]!
    seed := advance seed
    let c := atoms[seed % atoms.size]!
    let e := match kind with
      | 0 => .app a b
      | 1 => .lam `x a b .implicit
      | 2 => .forallE `x a b .default
      | 3 => .letE `x a b c (seed % 2 == 0)
      | 4 => .proj `Struct (seed % 4) a
      | _ => .mdata {} a
    pool := pool.push e
  let shared := mkApp (.bvar 1) (f `x)
  return pool.push (.app shared (.lam `x (.sort .zero) shared .default))
    |>.push (.lam `x (.bvar 0) (.lam `y (.bvar 1) (.app (.bvar 0) (.bvar 3)) .default) .default)

private def generate : M Unit := do
  let mut seed := 51923
  for e in samples do
    discard <| emit e
    if !e.hasLooseBVars then operation 9 e e.cheapBetaReduce #[]
    seed := advance seed
    let amount := seed % 4
    operation 0 e (e.liftLooseBVars 0 amount) #[] amount
    seed := advance seed
    let vs := (#[atoms[seed % atoms.size]!, .bvar 2, f `x]).extract 0 (seed % 4)
    let pairs ← vs.mapM fun e => do pure (0, ← emit e)
    operation 1 e (e.instantiate vs) pairs
    operation 2 e (e.instantiateRev vs) pairs
    let xs := #[f `x, f `y, f `x, .sort .zero]
    let n := seed % 6
    let selected :=  xs.extract 0 n
    let pairs ← selected.mapM fun e => do pure (0, ← emit e)
    operation 3 e (e.abstract selected) pairs
    let allPairs ← xs.mapM fun e => do pure (0, ← emit e)
    operation 6 e (e.abstractRange n xs) allPairs n
    let replacement : Expr := .bvar 1
    let single := #[(0, ← emit replacement)]
    operation 7 e (e.instantiate1 replacement) single
    operation 8 e (e.instantiate1 replacement) single
    let ps := [`u, `v, `u]
    let us := [Level.succ v, .zero, .param `w]
    let mut levelPairs := #[]
    for (p,u) in ps.zip us do levelPairs := levelPairs.push (← nameId p, ← emitLevel u)
    operation 4 e (e.instantiateLevelParams ps us) levelPairs
    let rs := #[(Expr.bvar 1, f `z), (.sort .zero, .bvar 2)]
    let pairs ← rs.mapM fun (a,b) => do pure (← emit a, ← emit b)
    operation 5 e (e.replace fun e => rs.findSome? fun (a,b) => if e == a then some b else none) pairs

private def betaCases : M Unit := do
  let ty := Expr.sort .zero
  let lam := fun b => Expr.lam `x ty b .default
  for body in #[ty, .bvar 0, .bvar 1, .app (.bvar 1) (.bvar 0), lam (.bvar 0), lam (.bvar 2)] do
    let fn := lam (lam body)
    for args in #[#[ty], #[ty, f `x], #[ty, f `x, f `y]] do
      let e := mkAppN fn args
      operation 9 e e.cheapBetaReduce #[]

def main : IO Unit := do
  discard <| (generate *> betaCases).run {}
