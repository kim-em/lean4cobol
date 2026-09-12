import Lean4Lean.TypeChecker

/- Small recursive-method budgets, including cache hits and direct primed calls.
   The expected outcome and successful result come from the pinned reference. -/
open Lean Lean4Lean

private structure EmitState where
  levels : Std.HashMap Level Nat := { (.zero, 0) }
  exprs : Std.HashMap Expr Nat := {}
  checks : Nat := 0

private abbrev M := StateT EmitState IO

private def emitLevel (l : Level) : M Nat := do
  if let some n := (← get).levels[l]? then return n
  let .succ u := l | throw <| IO.userError "unexpected test universe"
  let u ← emitLevel u
  let n := (← get).levels.size
  modify fun s => { s with levels := s.levels.insert l n }
  IO.println s!"L {n} 1 {u} 0 0 0"
  return n

private def emit (e : Expr) : M Nat := do
  if let some n := (← get).exprs[e]? then return n
  let (k, a, b, c) ← match e with
    | .sort u => do pure (1, ← emitLevel u, 0, 0)
    | .bvar i => pure (0, i, 0, 0)
    | .app f a => do pure (3, ← emit f, ← emit a, 0)
    | .lam _ d b _ => do pure (4, ← emit d, ← emit b, 0)
    | .forallE _ d b _ => do pure (5, ← emit d, ← emit b, 0)
    | .letE _ t v b _ => do pure (6, ← emit t, ← emit v, ← emit b)
    | .mdata _ b => do pure (11, ← emit b, 0, 0)
    | _ => throw <| IO.userError "unexpected test expression"
  let n := (← get).exprs.size + 1
  modify fun s => { s with exprs := s.exprs.insert e n }
  IO.println s!"E {n} {k} {a} {b} {c} 0"
  return n

private def operation (op : Nat) (e : Expr) : TypeChecker.M Expr := do
  match op with
  | 1 => TypeChecker.checkType e
  | 2 => TypeChecker.inferType e
  | 3 => TypeChecker.whnf e
  | 4 => TypeChecker.whnfCore e
  | _ => do
    unless ← TypeChecker.isDefEq e e do throw <| .other "reflexivity failed"
    return e

def main : IO Unit := do
  let prop := mkSort .zero
  let univ := mkSort (.succ .zero)
  let ident := mkLambda `T .default univ (.bvar 0)
  let applied := mkApp ident prop
  let choose := mkLambda `T .default univ (mkLambda `U .default univ (.bvar 1))
  let grouped := mkApp2 choose prop prop
  let lets := Expr.letE `T univ prop (.bvar 0) false
  let examples := [prop, .mdata {} prop, ident, applied, choose, grouped, lets,
    mkForall `T .default univ (mkForall `p .default (.bvar 0) univ)]
  let env ← Lean.mkEmptyEnvironment
  let work : M Unit := do
    for e in examples do
      let input ← emit e
      for op in [1, 2, 3, 4, 5] do
        for warm in [false, true] do
          for fuel in [0, 1, 2, 3, 4, 6] do
            let action : TypeChecker.M Expr := do
              if warm then
                discard <| withReader (fun c => { c with fuel.recDepth := 50000 }) (operation op e)
              operation op e
            let result := TypeChecker.M.run (env := env.toKernelEnv) (fuel := { recDepth := fuel }) (x := action)
            let (code, expected) ← match result with
              | .ok r => do pure (0, ← emit r)
              | .error (.deepRecursion) | .error (.deterministicTimeout) => pure (2, input)
              | .error _ => pure (1, input)
            modify fun s => { s with checks := s.checks + 1 }
            IO.println s!"Y {(← get).checks} {op + if warm then 10 else 0} {input} {expected} {fuel} {code}"
    for e in examples do
      let input ← emit e
      for whnf in [0, 1] do
        for whnfEager in [0, 1] do
          for eager in [false, true] do
            let action : TypeChecker.M Expr :=
              withReader (fun c => { c with eagerReduce := eager }) (operation 3 e)
            let result := TypeChecker.M.run (env := env.toKernelEnv)
              (fuel := { recDepth := 6, whnf, whnfEager }) (x := action)
            let (code, expected) ← match result with
              | .ok r => do pure (0, ← emit r)
              | .error (.deepRecursion) | .error (.deterministicTimeout) => pure (2, input)
              | .error _ => pure (1, input)
            modify fun s => { s with checks := s.checks + 1 }
            IO.println s!"Y {(← get).checks} 3 {input} {expected} 6 {code} {whnf} {whnfEager} {if eager then 1 else 0}"
  discard <| work.run {}
