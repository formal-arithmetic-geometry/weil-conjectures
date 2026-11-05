/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Flatness of signed powers of locally trivial lines -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange
attribute [local irreducible] monoidalCategory siteSheafTensorRight
attribute [local instance 2000] cochainModulesMonoidal
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  (A : Sheaf J CommRingCat.{max u v w})

private def chart_restrict (M : KFlatFixedTensor.Modules A) {V W : C}
    (e : M.over V ≅ unit
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over V)) (f : W ⟶ V) :
    M.over W ≅ unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over W) where
  hom := ⟨{ app := fun Z ↦ e.hom.val.app (op ((Over.map f).obj Z.unop))
            naturality := by
              intro Z Z' g
              exact e.hom.val.naturality ((Over.map f).op.map g) }⟩
  inv := ⟨{ app := fun Z ↦ e.inv.val.app (op ((Over.map f).obj Z.unop))
            naturality := by
              intro Z Z' g
              exact e.inv.val.naturality ((Over.map f).op.map g) }⟩
  hom_inv_id := by
    ext Z x
    exact congrArg (fun h ↦ h.val.app (op ((Over.map f).obj Z.unop)) x) e.hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun h ↦ h.val.app (op ((Over.map f).obj Z.unop)) x) e.inv_hom_id

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}] in
private theorem chart_sieve (M : KFlatFixedTensor.Modules A)
    (hM : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧ ∀ i,
      Nonempty (M.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over (V i)))) :
    ∀ U : C, ∃ s : Sieve U, s ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), s f →
      Nonempty (M.over V ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over V)) := by
  obtain ⟨I, V, hV, hM⟩ := hM
  intro U
  refine ⟨Sieve.ofObjects V U, hV U, ?_⟩
  rintro W f ⟨i, ⟨g⟩⟩
  exact ⟨chart_restrict A M (hM i).some g⟩

end SheafOfModules.SignedLineDerivedBaseChange
