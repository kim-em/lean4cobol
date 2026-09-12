import Lean4Lean.Level

/- Generates fixed-field records for tests/level-driver.cob using the pinned
lean4lean implementation as oracle. Run through tests/reference-levels.sh. -/
open Lean

private structure EmitState where
  ids : Std.HashMap Level Nat := { (.zero, 0) }
  next : Nat := 1

private def paramId (n : Name) : Nat :=
  if n == `u then 1 else if n == `v then 2 else if n == `w then 3 else 4

private def emit (l : Level) : StateT EmitState IO Nat := do
  if let some id := (← get).ids[l]? then return id
  let (k, a, b) ← match l with
    | .zero => pure (0, 0, 0)
    | .succ a => do pure (1, ← emit a, 0)
    | .max a b => do pure (2, ← emit a, ← emit b)
    | .imax a b => do pure (3, ← emit a, ← emit b)
    | .param n => pure (4, paramId n, 0)
    | .mvar _ => throw <| IO.userError "metavariables cannot occur in exports"
  let id := (← get).next
  modify fun s => { s with ids := s.ids.insert l id, next := id + 1 }
  IO.println s!"N {id} {k} {a} {b} 0"
  return id

private def levelsUpTo (n : Nat) : Array Level := Id.run do
  let mut tbl : Array (Array Level) := #[#[], #[.zero, .param `u, .param `v, .param `w]]
  for k in [2:n+1] do
    let mut out := tbl[k-1]!.map .succ
    for i in [1:k-1] do
      for a in tbl[i]! do
        for b in tbl[k-1-i]! do
          out := out.push (.max a b) |>.push (.imax a b)
    tbl := tbl.push out
  return tbl.foldl (· ++ ·) #[]

private def u : Level := .param `u
private def v : Level := .param `v
private def w : Level := .param `w
private def x : Level := .param `x

-- The five isEquiv'/geq' regressions from Lean4Lean/Tests/Level.lean.
private def regressions : Array (Nat × Level × Level) := #[
  (0, .max v (.max w (.imax (.imax (.imax u v) w) x)),
      .max v (.max w (.imax (.imax (.imax u w) v) x))),
  (1, .max (.ofNat 2) v, .imax (.ofNat 2) v),
  (1, .max (u.addOffset 2) v, .imax (u.addOffset 2) v),
  (0, .imax u (.max u v), .max u v),
  (0, .max v u, .max (.imax u v) u)]

private def check (seq mode : Nat) (a b : Level) : StateT EmitState IO Unit := do
  let lhs ← emit a
  let rhs ← emit b
  let expected := if mode == 0 then a.isEquiv' b else a.geq' b
  IO.println s!"C {seq} {mode} {lhs} {rhs} {if expected then 1 else 0}"
  IO.println s!"E {seq} 0 {lhs} {rhs} {if a.isEquiv b then 1 else 0}"

def main : IO Unit := do
  discard <| (do
    let mut seq := 0
    for (mode, a, b) in regressions do
      check seq mode a b
      seq := seq + 1
    let ls := levelsUpTo 5
    for l in ls do
      check seq 0 l l.normalize'
      check seq 0 l l.normalize
      seq := seq + 1
    let mut seed : Nat := 93457
    for _ in [:5000] do
      seed := (seed * 1664525 + 1013904223) % 4294967296
      let a := ls[seed % ls.size]!
      seed := (seed * 1664525 + 1013904223) % 4294967296
      let b := ls[seed % ls.size]!
      check seq 0 a b
      seq := seq + 1
      check seq 1 a b
      seq := seq + 1
    -- Deeper DAGs exercise nested imax, offset distribution, and merging
    -- max terms. Only native equality is queried here (the complete algebra
    -- is independently covered above).
    let mut deep := ls
    for _ in [:2000] do
      seed := (seed * 1664525 + 1013904223) % 4294967296
      let a := deep[seed % deep.size]!
      seed := (seed * 1664525 + 1013904223) % 4294967296
      let b := deep[seed % deep.size]!
      let l := match seed % 3 with
        | 0 => .succ a
        | 1 => .max a b
        | _ => .imax a b
      deep := deep.push l
      for (a, b) in #[(l, l.normalize), (.max a b, .max b a), (a, b)] do
        let ai ← emit a
        let bi ← emit b
        IO.println s!"E {seq} 0 {ai} {bi} {if a.isEquiv b then 1 else 0}"
        seq := seq + 1
    : StateT EmitState IO Unit).run {}
