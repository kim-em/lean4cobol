import Export

/- Exercise literal/constructor equality in both directions, scalar decoding,
   and generated string recursors without depending on a frontend evaluator. -/
theorem stringEmpty : String.ofList [] = "" := rfl
theorem stringASCII : String.ofList ['a', 'b', 'c'] = "abc" := rfl
theorem stringUnicode : String.ofList ['é', 'λ', '😀'] = "éλ😀" := rfl
theorem stringReverse : "éλ😀" = String.ofList ['é', 'λ', '😀'] := rfl
theorem stringNul : String.ofList [Char.ofNat 0, Char.ofNat 127, Char.ofNat 128,
    Char.ofNat 2047, Char.ofNat 2048, Char.ofNat 55295, Char.ofNat 57344,
    Char.ofNat 65535, Char.ofNat 65536, Char.ofNat 1114111] =
  "\x00\x7f\u0080\u07ff\u0800\ud7ff\ue000\uffff𐀀􏿿" := rfl

noncomputable def stringRecursor (s : String) : Nat :=
  String.rec (motive := fun _ => Nat) (fun _ _ => 37) s

theorem stringRecursorEmpty : stringRecursor "" = 37 := rfl
theorem stringRecursorUnicode : stringRecursor "éλ😀" = 37 := rfl

theorem stringProjection : "éλ😀".toByteArray = (String.ofList ['é', 'λ', '😀']).toByteArray := rfl

def stringLiteralOnly : String := "éλ😀"
def stringLiteralBinder (_ : Nat) : String := "abc"
axiom stringTypeOnly : ("éλ😀" = "éλ😀")

run_meta do
  -- New scalar numeral blobs force byte-arena growth while expanding this
  -- literal; none of those explicit character values occur in the export.
  let text := String.ofList ((List.range 8192).map fun i => Char.ofNat (65536 + i))
  let nat := Lean.mkConst ``Nat
  let value := Lean.mkNatLit 37
  let lhs := Lean.mkApp (Lean.mkConst ``stringRecursor) (Lean.mkStrLit text)
  let type := Lean.mkApp3 (Lean.mkConst ``Eq [Lean.Level.one]) nat lhs value
  let proof := Lean.mkApp2 (Lean.mkConst ``Eq.refl [Lean.Level.one]) nat value
  Lean.addDecl (.thmDecl { name := `stringRecursorLong, levelParams := [], type, value := proof })
  let env ← Lean.getEnv
  let _ ← M.run env do
    initState env
    dumpMetadata
    dumpConstant ``stringProjection
    dumpConstant ``stringLiteralOnly
    dumpConstant ``stringLiteralBinder
    dumpConstant ``stringTypeOnly
    dumpConstant ``stringEmpty
    dumpConstant ``stringASCII
    dumpConstant ``stringUnicode
    dumpConstant ``stringReverse
    dumpConstant ``stringNul
    dumpConstant ``stringRecursorEmpty
    dumpConstant ``stringRecursorUnicode
    dumpConstant `stringRecursorLong
