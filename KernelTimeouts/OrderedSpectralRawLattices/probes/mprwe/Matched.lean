module
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement

@[expose] public noncomputable section
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

example
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X)) :
    (CondensedRing.upperStar A f).obj M =
    (CondensedRing.upperStar A f).obj ((fun Z => Z) M) := by
  have h : (CondensedRing.upperStar A f).obj ((fun Z => Z) M) =
      (CondensedRing.upperStar A f).obj M := by rfl
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let h ← Lean.Meta.getFVarFromUserName `h
      let actual ← Lean.Meta.inferType h
      let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
      Lean.logInfo m!"matched pair syntactic={actual == expected}"
  exact h

end AlgebraicGeometry.ProEtale
