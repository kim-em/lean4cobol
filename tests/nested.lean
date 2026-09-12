import Export

/- Nested occurrences exercise auxiliary inductives, constructor restoration,
   public recursor renaming, and recursor reduction after restoration. -/
universe u
inductive NestedRose (α : Type u) : Type u where
  | node : α → List (NestedRose α) → NestedRose α
inductive NestedArray (α : Type u) : Type u where
  | node : α → Array (NestedArray α) → NestedArray α

inductive NestedDouble (α : Type u) : Type u where
  | node : List (List (NestedDouble α)) → NestedDouble α
inductive NestedReuse (α : Type u) : Type u where
  | node : List (NestedReuse α) → List (NestedReuse α) → NestedReuse α
inductive NestedIndexed (α : Type u) : Nat → Type u where
  | node : List (NestedIndexed α Nat.zero) → NestedIndexed α (Nat.succ Nat.zero)
inductive NestedFunction (α : Type u) : Type u where
  | node : (Nat → List (NestedFunction α)) → NestedFunction α
inductive NestedFunctionParameter (α : Type u) : Type u where
  | node : List (Nat → NestedFunctionParameter α) → NestedFunctionParameter α
inductive NestedDependent (α : Type u) (a : α) : Type u where
  | node : List (NestedDependent α a) → NestedDependent α a
inductive NestedProp : Prop where
  | node : And NestedProp NestedProp → NestedProp
mutual
  inductive NestContainerTree (α : Type u) : Type u where
    | leaf : α → NestContainerTree α
    | branch : NestContainerForest α → NestContainerTree α
  inductive NestContainerForest (α : Type u) : Type u where
    | nil : NestContainerForest α
    | cons : NestContainerTree α → NestContainerForest α → NestContainerForest α
end
inductive NestedMutualContainer (α : Type u) : Type u where
  | node : NestContainerTree (NestedMutualContainer α) → NestedMutualContainer α

def NestedRose.label : NestedRose α → α
  | .node a _ => a

theorem nestedReduction (a : α) : NestedRose.label (NestedRose.node a []) = a := rfl

run_meta do
  let env ← Lean.getEnv
  let _ ← M.run env do
    initState env
    dumpMetadata
    dumpConstant ``NestedRose
    dumpConstant ``NestedArray
    dumpConstant ``NestedDouble
    dumpConstant ``NestedReuse
    dumpConstant ``NestedIndexed
    dumpConstant ``NestedFunction
    dumpConstant ``NestedFunctionParameter
    dumpConstant ``NestedDependent
    dumpConstant ``NestedProp
    dumpConstant ``NestedMutualContainer
    dumpConstant ``nestedReduction
