/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueDerivedMonoidal
public import WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
/-! # Tensor compatibility of a square of exact derived functors -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
universe u a b c d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory
section TensorMonoidal
open Category Functor.OplaxMonoidal Functor.Monoidal
variable {E H : Type*} [Category E] [Category H]
  [MonoidalCategory E] [MonoidalCategory H]
  {F G : E ⥤ H} [mF : F.Monoidal] [mG : G.Monoidal] (e : F ≅ G)
  (hd : ∀ X Y, e.hom.app (X ⊗ Y) ≫ δ G X Y =
    δ F X Y ≫ (e.hom.app X ⊗ₘ e.hom.app Y))
include hd in
end TensorMonoidal
end CategoryTheory
namespace CategoryTheory
section CompareStructures
open Category Functor.OplaxMonoidal Functor.LaxMonoidal
variable {E H : Type*} [Category E] [Category H]
  [MonoidalCategory E] [MonoidalCategory H] (F : E ⥤ H)
  (m n : F.Monoidal)
  (hd : ∀ X Y, @δ _ _ _ _ _ _ F m.toOplaxMonoidal X Y =
    @δ _ _ _ _ _ _ F n.toOplaxMonoidal X Y)
include hd in

private theorem monoidal_of_tensor_iso : NatTrans.IsMonoidal e.hom := by
  let m : G.Monoidal := Functor.Monoidal.transport e
  have hδ (X Y : E) : @δ _ _ _ _ _ _ G m.toOplaxMonoidal X Y =
      @δ _ _ _ _ _ _ G mG.toOplaxMonoidal X Y := by
    rw [Functor.Monoidal.transport_δ]
    rw [← hd X Y]
    simp only [Iso.inv_hom_id_app_assoc]
  have : IsIso (@δ _ _ _ _ _ _ G mG.toOplaxMonoidal (𝟙_ E) (𝟙_ E)) := by
    letI := mG
    infer_instance
  have hη : @η _ _ _ _ _ _ G m.toOplaxMonoidal =
      @η _ _ _ _ _ _ G mG.toOplaxMonoidal := by
    apply Functor.eq_of_leftUnitality
      (@δ _ _ _ _ _ _ G mG.toOplaxMonoidal (𝟙_ E) (𝟙_ E))
    · rw [← hδ]
      exact @left_unitality_hom _ _ _ _ _ _ G m.toOplaxMonoidal (𝟙_ E)
    · exact @left_unitality_hom _ _ _ _ _ _ G mG.toOplaxMonoidal (𝟙_ E)
  letI := mG
  apply ExactMonoidalEquivalenceDerived.monoidal_of_oplax e.hom
  · rw [← hη, Functor.Monoidal.transport_η]
    simp only [Iso.hom_inv_id_app_assoc]
  · exact hd

/-- The invertible tensor comparison determines the monoidal structure, including its unit.
Source: the monoidal unit axioms and uniqueness of inverses.
-/
private theorem monoidal_eq_of_delta : m = n := by
  letI := m
  have hu : @η _ _ _ _ _ _ F m.toOplaxMonoidal =
      @η _ _ _ _ _ _ F n.toOplaxMonoidal := by
    apply Functor.eq_of_leftUnitality (δ F (𝟙_ E) (𝟙_ E))
    · exact Functor.OplaxMonoidal.left_unitality_hom F (𝟙_ E)
    · rw [hd]
      exact @Functor.OplaxMonoidal.left_unitality_hom _ _ _ _ _ _ F n.toOplaxMonoidal (𝟙_ E)
  have hμ (X Y : E) : @μ _ _ _ _ _ _ F m.toLaxMonoidal X Y =
      @μ _ _ _ _ _ _ F n.toLaxMonoidal X Y := by
    apply (cancel_mono (δ F X Y)).1
    rw [Functor.Monoidal.μ_δ, hd]
    exact (@Functor.Monoidal.μ_δ _ _ _ _ _ _ F n X Y).symm
  have hε : @ε _ _ _ _ _ _ F m.toLaxMonoidal =
      @ε _ _ _ _ _ _ F n.toLaxMonoidal := by
    apply (cancel_mono (η F)).1
    rw [Functor.Monoidal.ε_η, hu]
    exact (@Functor.Monoidal.ε_η _ _ _ _ _ _ F n).symm
  apply Functor.Monoidal.ext
  · exact hε
  · exact funext fun X ↦ funext fun Y ↦ hμ X Y
  · exact hu
  · exact funext fun X ↦ funext fun Y ↦ hd X Y
end CompareStructures
end CategoryTheory
namespace CategoryTheory.Functor
variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F₁ : A ⥤ B) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  (F₂ : B ⥤ D) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  (G₁ : A ⥤ C) [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  (G₂ : C ⥤ D) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]
  (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) [NatTrans.IsMonoidal τ.hom]
private def pairIso : F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor ≅
    F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory :=
  isoWhiskerRight F₁.leftDerivedFunctorIsoMapDerivedCategory _ ≪≫
    isoWhiskerLeft _ F₂.leftDerivedFunctorIsoMapDerivedCategory

private theorem square_iso_normalization :
    ((mapDerivedCategoryCompIso G₁ G₂).symm ≪≫ mapDerivedCategoryNatIso τ ≪≫
      mapDerivedCategoryCompIso F₁ F₂).hom =
      (pairIso G₁ G₂).inv ≫
        (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom ≫ (pairIso F₁ F₂).hom := by
  apply NatTrans.ext
  funext X
  simp only [pairIso, leftDerivedFunctorCompNatIso, leftDerivedFunctorCompIso,
    leftDerivedFunctorNatIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerRight_inv,
    isoWhiskerLeft_hom, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [G₂.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  rw [← F₂.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, ← Functor.map_comp, Functor.map_id, Category.id_comp,
    Category.comp_id]
  erw [Category.comp_id]

private theorem left_square_tensor (K M : DerivedCategory A) :
    letI := F₁.residueDerivedMonoidal
    letI := F₂.residueDerivedMonoidal
    letI := G₁.residueDerivedMonoidal
    letI := G₂.residueDerivedMonoidal
    (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app (K ⊗ M) ≫
        OplaxMonoidal.δ (F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor) K M =
      OplaxMonoidal.δ (G₁.leftDerivedFunctor ⋙ G₂.leftDerivedFunctor) K M ≫
        ((leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app K ⊗ₘ
          (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom.app M) := by
  letI := F₁.residueDerivedMonoidal
  letI := F₂.residueDerivedMonoidal
  letI := G₁.residueDerivedMonoidal
  letI := G₂.residueDerivedMonoidal
  change _ ≫ (F₂.leftDerivedFunctor.map ((F₁.leftDerivedTensorComparison.app K).app M) ≫
    (F₂.leftDerivedTensorComparison.app (F₁.leftDerivedFunctor.obj K)).app
      (F₁.leftDerivedFunctor.obj M)) =
    (G₂.leftDerivedFunctor.map ((G₁.leftDerivedTensorComparison.app K).app M) ≫
      (G₂.leftDerivedTensorComparison.app (G₁.leftDerivedFunctor.obj K)).app
        (G₁.leftDerivedFunctor.obj M)) ≫ _
  rw [map_leftDerivedTensorComparison_comp_eq_of_iso F₁ F₂ G₁ G₂ τ K M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem left_square_monoidal :
    letI := F₁.residueDerivedMonoidal
    letI := F₂.residueDerivedMonoidal
    letI := G₁.residueDerivedMonoidal
    letI := G₂.residueDerivedMonoidal
    NatTrans.IsMonoidal (leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ).hom := by
  letI := F₁.residueDerivedMonoidal
  letI := F₂.residueDerivedMonoidal
  letI := G₁.residueDerivedMonoidal
  letI := G₂.residueDerivedMonoidal
  apply monoidal_of_tensor_iso
  exact left_square_tensor F₁ F₂ G₁ G₂ τ

private theorem pair_monoidal :
    letI := F₁.residueDerivedMonoidal
    letI := F₂.residueDerivedMonoidal
    letI := Functor.Monoidal.transport F₁.leftDerivedFunctorIsoMapDerivedCategory
    letI := Functor.Monoidal.transport F₂.leftDerivedFunctorIsoMapDerivedCategory
    NatTrans.IsMonoidal (pairIso F₁ F₂).hom := by
  letI := F₁.residueDerivedMonoidal
  letI := F₂.residueDerivedMonoidal
  letI := Functor.Monoidal.transport F₁.leftDerivedFunctorIsoMapDerivedCategory
  letI := Functor.Monoidal.transport F₂.leftDerivedFunctorIsoMapDerivedCategory
  have := Functor.Monoidal.natTransIsMonoidal_of_transport
    F₁.leftDerivedFunctorIsoMapDerivedCategory
  have := Functor.Monoidal.natTransIsMonoidal_of_transport
    F₂.leftDerivedFunctorIsoMapDerivedCategory
  dsimp only [pairIso, Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

private theorem exactDerivedMonoidal_eq_of_delta (m : F₁.mapDerivedCategory.Monoidal)
    (hd : ∀ K M, @OplaxMonoidal.δ _ _ _ _ _ _ F₁.mapDerivedCategory
      m.toOplaxMonoidal K M =
      F₁.leftDerivedFunctorIsoMapDerivedCategory.inv.app (K ⊗ M) ≫
        (F₁.leftDerivedTensorComparison.app K).app M ≫
          (F₁.leftDerivedFunctorIsoMapDerivedCategory.hom.app K ⊗ₘ
            F₁.leftDerivedFunctorIsoMapDerivedCategory.hom.app M)) :
    m = exactClosedDerivedMonoidal F₁ := by
  unfold exactClosedDerivedMonoidal
  letI := F₁.residueDerivedMonoidal
  apply monoidal_eq_of_delta
  intro K M
  rw [hd, Functor.Monoidal.transport_δ]
  rfl

/-- A monoidal square of exact functors induces a monoidal square of derived functors
with the canonical transported tensor structures. Source: deriving tensor comparisons,
Stacks Project, Tag 07A4. The derived square is conjugate to the left-derived square by
the exact-functor identifications. The tensor square for left-derived comparisons proves
monoidality there; tensor compatibility also determines the unit map.
(blueprint: lem-sf-exact-derived-tensor-square) -/
theorem exactDerivedSquare_monoidal :
    letI := exactClosedDerivedMonoidal F₁
    letI := exactClosedDerivedMonoidal F₂
    letI := exactClosedDerivedMonoidal G₁
    letI := exactClosedDerivedMonoidal G₂
    NatTrans.IsMonoidal ((mapDerivedCategoryCompIso G₁ G₂).symm ≪≫
      mapDerivedCategoryNatIso τ ≪≫ mapDerivedCategoryCompIso F₁ F₂).hom := by
  unfold exactClosedDerivedMonoidal
  letI := F₁.residueDerivedMonoidal
  letI := F₂.residueDerivedMonoidal
  letI := G₁.residueDerivedMonoidal
  letI := G₂.residueDerivedMonoidal
  letI := Functor.Monoidal.transport F₁.leftDerivedFunctorIsoMapDerivedCategory
  letI := Functor.Monoidal.transport F₂.leftDerivedFunctorIsoMapDerivedCategory
  letI := Functor.Monoidal.transport G₁.leftDerivedFunctorIsoMapDerivedCategory
  letI := Functor.Monoidal.transport G₂.leftDerivedFunctorIsoMapDerivedCategory
  have := pair_monoidal F₁ F₂
  have := pair_monoidal G₁ G₂
  have := left_square_monoidal F₁ F₂ G₁ G₂ τ
  rw [square_iso_normalization]
  infer_instance

end CategoryTheory.Functor
