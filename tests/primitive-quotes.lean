import Lean4Lean.Primitive
/- Compile-time quotations from the pinned Primitive.lean. Holes are COBOL context handles. -/
open Lean Lean4Lean.Environment
private def hole (s : String) : Expr := .fvar ⟨.str .anonymous s⟩
private def prop := q(Prop)
private def nat := q(Nat)
private def zero := q(Nat.zero)
private def one := mkApp q(Nat.succ) zero
private def succ := mkApp q(Nat.succ)
private def arrow := Expr.arrow
private def rt := hole "r-type"
private def p := hole "p"
private def H := hole "hyp"
private def a := hole "a"
private def b := hole "b"
private def x := hole "x"
private def y := hole "y"
private def hy := hole "hy"
private def fuel := hole "fuel"
private def h := hole "h"
private def val := hole "value"
private def go := hole "go"
private def le := mkApp2 Condition.natLE.prop
private def sub := mkApp2 q(Nat.sub)
private def cprop := hole "c-prop"
private def cdec := hole "c-dec"
private def cite (ty : Expr) (args : Array Expr) (t e : Expr) : Expr :=
  mkApp5 q(@ite.{1}) ty (mkAppN cprop args) (mkAppN cdec args) t e
private def cdite (args : Array Expr) (t e : Expr) : Expr :=
  mkApp4 q(@dite Nat) (mkAppN cprop args) (mkAppN cdec args)
    (.lam0 (mkAppN cprop args) t) (.lam0 (mkApp q(Not) (mkAppN cprop args)) e)
private def quotations : Array (String × Expr) := Id.run do
  let mut qs := #[]
  for (tag, r) in [("r1", Reflection.defn₁), ("r2", Reflection.defn₂)] do
    qs := qs ++ #[(tag ++ ".type", r.type), (tag ++ ".true", r.ofTrue),
      (tag ++ ".false", r.ofFalse), (tag ++ ".dec", r.toDec),
      (tag ++ ".ite", r.ite), (tag ++ ".dite", r.natDITE)]
  for (tag,c) in [("le", Condition.natLE), ("eq", Condition.natEq), ("bool", Condition.bool)] do
    qs := qs ++ #[(tag ++ ".prop", c.prop), (tag ++ ".dec", c.dec)]
    if let .reflectNatNat asBool _ proof := c.impl then
      qs := qs ++ #[(tag ++ ".asBool", asBool), (tag ++ ".proof", proof)]
  let typeITE := arrow prop <| arrow q(Bool) <|
    arrow (mkApp2 rt (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)
  let typeDITE := arrow prop <| arrow q(Bool) <|
    arrow (mkApp2 rt (.bvar 1) (.bvar 0)) <|
    arrow (arrow (.bvar 2) nat) <| arrow (arrow (mkApp q(Not) (.bvar 3)) nat) nat
  let sx := succ x
  let recCall := mkApp5 go y hy fuel (sub x y)
    (mkApp6 q(@Nat.div_rec_fuel_lemma) x y fuel hy (.bvar 0) h)
  qs := qs ++ #[
    ("Prop", prop), ("Nat", nat), ("Not", q(Not)), ("not.type", q(Prop → Prop)),
    ("r.typeExpected", q(Prop → Bool → Prop)),
    ("r.iteExpected", typeITE), ("r.diteExpected", typeDITE),
    ("r.trueExpected", arrow prop <| arrow (mkApp2 rt (.bvar 0) q(true)) (.bvar 1)),
    ("r.falseExpected", arrow prop <| arrow (mkApp2 rt (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))),
    ("r.trueHyp", mkApp2 rt p q(true)), ("r.falseHyp", mkApp2 rt p q(false)),
    ("r.aType", arrow p nat), ("r.bType", arrow (mkApp q(Not) p) nat),
    ("r.iteTrue", mkApp3 (hole "r-ite") p q(true) H),
    ("r.iteFalse", mkApp3 (hole "r-ite") p q(false) H),
    ("r.iteTrueExpected", q(fun α : Type => fun a _ : α => a)),
    ("r.iteFalseExpected", q(fun α : Type => fun _ a : α => a)),
    ("r.diteTrue", mkApp5 (hole "r-dite") p q(true) H a b),
    ("r.diteFalse", mkApp5 (hole "r-dite") p q(false) H a b),
    ("r.diteTrueExpected", mkApp a (mkApp2 (hole "r-true") p H)),
    ("r.diteFalseExpected", mkApp b (mkApp2 (hole "r-false") p H)),
    ("c.propExpected", q(Nat → Nat → Prop)), ("c.boolExpected", q(Nat → Nat → Bool)),
    ("c.decBody", .lam0 nat <| .lam0 nat <| mkApp3 (hole "r-dec")
      (mkApp2 cprop (.bvar 1) (.bvar 0)) (mkApp2 (hole "as-bool") (.bvar 1) (.bvar 0))
      (mkApp2 (hole "c-proof") (.bvar 1) (.bvar 0))),
    ("bool.propExpected", q(Bool → Prop)),
    ("bool.natITE", .lam0 q(Bool) <| mkApp2 q(@ite Nat) (mkApp cprop (.bvar 0)) (mkApp cdec (.bvar 0))),
    ("bool.iteExpected", q(Bool → Nat → Nat → Nat)),
    ("bool.iteTrue", mkApp (hole "r-ite") q(true)),
    ("bool.iteFalse", mkApp (hole "r-ite") q(false)),
    ("bool.iteTrueExpected", q(fun a _ : Nat => a)),
    ("bool.iteFalseExpected", q(fun _ a : Nat => a)),
    ("mod.zero", arrow nat (mkApp2 val zero (.bvar 0))),
    ("mod.zeroExpected", arrow nat zero),
    ("mod.go", q(Nat.modCore.go)), ("div.go", q(Nat.div.go)),
    ("division.goType", q(∀ n, Nat.succ Nat.zero ≤ n → ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat)),
    ("mod.initial", cite nat #[y, sx] (cdite #[one, y]
      (mkApp5 go y (.bvar 0) (succ sx) sx (mkApp q(Nat.lt_succ_self) sx)) sx) sx),
    ("mod.initialLhs", mkApp2 val sx y), ("mod.recursive", cdite #[y, x] recCall x),
    ("div.initial", cdite #[one, y]
      (mkApp5 go y (.bvar 0) (succ x) x (mkApp q(Nat.lt_succ_self) x)) zero),
    ("div.initialLhs", mkApp2 val x y), ("div.recursive", cdite #[y, x] (succ recCall) zero),
    ("division.recursiveLhs", mkApp5 go y hy (succ fuel) x h),
    ("division.hyType", le one y), ("division.hType", le (succ x) (succ fuel))]
  let ce := Condition.natEq
  let cb := Condition.bool
  let two := succ one
  let n' := mkApp2 q(Nat.div) x two
  let m' := mkApp2 q(Nat.div) y two
  let b₁ := ce.decide #[mkApp2 q(Nat.mod) x two, one]
  let b₂ := ce.decide #[mkApp2 q(Nat.mod) y two, one]
  let r := mkApp3 val a n' m'
  let rr := mkApp2 q(Nat.add) r r
  let bitwiseRhs :=
    ce.ite nat #[x, zero] (cb.ite nat #[mkApp2 a q(false) q(true)] y zero) <|
    ce.ite nat #[y, zero] (cb.ite nat #[mkApp2 a q(true) q(false)] x zero) <|
    cb.ite nat #[mkApp2 a b₁ b₂] (mkApp2 q(Nat.add) rr one) rr
  qs := qs ++ #[
    ("wf.gcdEqDef", q(type_of% Nat.gcd.eq_def)),
    ("wf.bitwiseEqDef", q(type_of% Nat.bitwise.eq_def)),
    ("wf.eagerLhs", arrow nat (mkApp a (.bvar 0))),
    ("wf.eagerRhs", arrow nat (cb.ite nat #[mkApp2 q(Nat.beq) (.bvar 0) (.bvar 0)] (.bvar 0) (.bvar 0))),
    ("gcd.zeroLhs", mkApp2 go zero x),
    ("gcd.succLhs", mkApp2 go (succ y) x),
    ("gcd.succRhs", mkApp2 val (mkApp2 q(Nat.mod) x (succ y)) (succ y)),
    ("bitwise.type", q((Bool → Bool → Bool) → Nat → Nat → Nat)),
    ("bitwise.functionType", q(Bool → Bool → Bool)),
    ("bitwise.lhs", mkApp3 go a x y),
    ("bitwise.rhs", bitwiseRhs)]
  return qs
private def arr (xs : List Json) := Json.arr xs.toArray
private def num (n : Nat) := toJson n
private partial def levelJson : Level → Json
  | .zero => arr [num 0]
  | .succ a => arr [num 1, levelJson a]
  | .max a b => arr [num 2, levelJson a, levelJson b]
  | .imax a b => arr [num 3, levelJson a, levelJson b]
  | .param n => arr [num 4, toJson n.toString]
  | .mvar _ => panic! "metavariable in quotation"
private partial def exprJson : Expr → Json
  | .bvar n => arr [num 0, num n]
  | .sort u => arr [num 1, levelJson u]
  | .const n us => arr [num 2, toJson n.toString, toJson (us.map levelJson)]
  | .app f a => arr [num 3, exprJson f, exprJson a]
  | .lam _ a b _ => arr [num 4, exprJson a, exprJson b]
  | .forallE _ a b _ => arr [num 5, exprJson a, exprJson b]
  | .letE _ t v b nd => arr [num 6, exprJson t, exprJson v, exprJson b, toJson nd]
  | .proj n i s => arr [num 7, toJson n.toString, num i, exprJson s]
  | .lit (.natVal n) => arr [num 8, toJson (toString n)]
  | .lit (.strVal s) => arr [num 9, toJson s]
  | .fvar ⟨n⟩ => arr [num 10, toJson n.toString]
  | .mdata _ e => arr [num 11, exprJson e]
  | .mvar _ => panic! "metavariable in quotation"
def main : IO Unit := do
  for (name,e) in quotations do
    IO.println (Json.mkObj [("name", toJson name), ("expr", exprJson e)]).compress
