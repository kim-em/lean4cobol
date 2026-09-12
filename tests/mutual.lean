import Export

/- Focused mutual-block coverage before nested elimination reuses this path. -/
universe u
mutual
  inductive BranchTree (α : Type u) : Type u where
    | leaf : α → BranchTree α
    | branch : BranchForest α → BranchTree α
  inductive BranchForest (α : Type u) : Type u where
    | nil : BranchForest α
    | cons : BranchTree α → BranchForest α → BranchForest α
end
mutual
  inductive StepEven : Nat → Prop where
    | zero : StepEven Nat.zero
    | step {n} : StepOdd n → StepEven (Nat.succ n)
  inductive StepOdd : Nat → Prop where
    | step {n} : StepEven n → StepOdd (Nat.succ n)
end

mutual
  def treeWeight : BranchTree α → Nat
    | .leaf _ => Nat.zero
    | .branch forest => forestWeight forest
  def forestWeight : BranchForest α → Nat
    | .nil => Nat.zero
    | .cons tree rest => Nat.succ (Nat.add (treeWeight tree) (forestWeight rest))
end

theorem mutualReduction :
    treeWeight (BranchTree.branch (BranchForest.cons (BranchTree.leaf PUnit.unit) BranchForest.nil)) =
      Nat.succ Nat.zero := rfl

run_meta do
  let env ← Lean.getEnv
  let _ ← M.run env do
    initState env
    dumpMetadata
    dumpConstant ``BranchTree
    dumpConstant ``BranchForest
    dumpConstant ``StepEven
    dumpConstant ``StepOdd
    dumpConstant ``mutualReduction
