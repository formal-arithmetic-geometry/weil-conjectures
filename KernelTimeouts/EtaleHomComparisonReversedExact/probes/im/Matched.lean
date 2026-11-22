module
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels

set_option autoImplicit false
@[expose] public noncomputable section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale

example {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M K : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M) :
    v.app (op K) = v.app (op ((fun Z => Z) K)) := by
  have h : v.app (op ((fun Z => Z) K)) = v.app (op K) := by rfl
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let h ← Lean.Meta.getFVarFromUserName `h
      let actual ← Lean.Meta.inferType h
      let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
      Lean.logInfo m!"matched pair syntactic={actual == expected}"
  exact h

example {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v) :
    IsEtaleHomTranspose X φ M ((fun w => w) v) := by
  have h : IsEtaleHomTranspose X φ M v := hv
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let h ← Lean.Meta.getFVarFromUserName `h
      let actual ← Lean.Meta.inferType h
      let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
      Lean.logInfo m!"proposition pair syntactic={actual == expected}"
  exact h

end AlgebraicGeometry.Etale
