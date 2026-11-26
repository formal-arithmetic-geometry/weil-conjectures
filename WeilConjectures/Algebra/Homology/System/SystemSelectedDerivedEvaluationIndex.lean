/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedEvaluation

/-! # Derived evaluation of subsequence extension

## References

* Stacks Project, Tags 03D7, 03EK
* Zheng 4.1
* Zheng, Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (r : ℕ ↪o ℕ) (m : ℕ)

/-- Reindex the evaluated derived extension along an equality of selected indices. -/
def systemSelectedDerivedBelowIndex {i : ℕ} (hi : systemNextSelected r m = i)
    (h : m ≤ r i) :
    (systemSelectedDerivedExtension B r S T).derived ⋙ derivedSystemEvaluation B m ≅
      derivedSystemEvaluation (selectedSystemRings B r) i ⋙ systemDerivedTensor S B h := by
  subst i
  exact systemSelectedDerivedBelow B r m S T

/-- Reindexing preserves the normalized transpose formula. -/
theorem systemSelectedDerivedBelowIndex_transpose {i : ℕ}
    (hi : systemNextSelected r m = i) (h : m ≤ r i)
    (P : DerivedCategory (StrictRingSystem (selectedSystemRings B r)))
    (M : DerivedCategory (StrictRingSystem B))
    (f : (systemSelectedDerivedExtension B r S T).derived.obj P ⟶ M) :
    (systemDerivedTensorAdj S B h).homEquiv _ _
      ((systemSelectedDerivedBelowIndex S T B r m hi h).inv.app P ≫
        (derivedSystemEvaluation B m).map f) =
    (derivedSystemEvaluation (selectedSystemRings B r) i).map
      ((systemSelectedDerivedExtension B r S T).adjunction.homEquiv P M f) ≫
      (systemDerivedSubsequenceEvaluation B r i).hom.app M ≫
      (systemDerivedTransition B h).app M := by
  subst i
  exact systemSelectedDerivedTranspose S T B r m P M f

/-- The reindexed comparison is the original comparison followed by the object
transport. -/
theorem systemSelectedDerivedBelowIndex_hom {i : ℕ}
    (hi : systemNextSelected r m = i) (h : m ≤ r i)
    (P : DerivedCategory (StrictRingSystem (selectedSystemRings B r)))
    (he : (systemDerivedTensor S B (systemNextSelected_spec r m).1).obj
        ((derivedSystemEvaluation (selectedSystemRings B r) (systemNextSelected r m)).obj P) =
      (systemDerivedTensor S B h).obj
        ((derivedSystemEvaluation (selectedSystemRings B r) i).obj P)) :
    (systemSelectedDerivedBelowIndex S T B r m hi h).hom.app P =
      (systemSelectedDerivedBelow B r m S T).hom.app P ≫ eqToHom he := by
  subst i
  dsimp only [systemSelectedDerivedBelowIndex]
  erw [eqToHom_refl, Category.comp_id]

end SheafOfModules
