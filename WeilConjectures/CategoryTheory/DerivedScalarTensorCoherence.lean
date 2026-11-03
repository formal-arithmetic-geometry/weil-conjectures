/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
/-! # Tensor coherence from the counit normalization of derived scalar transitivity -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor DerivedCategory
namespace CategoryTheory
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  {E : Type u₃} [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [MonoidalClosed E] [BraidedCategory E] [Abelian.HasFunctorialFlatResolution E]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
  [F.IsLeftAdjoint] [F.Monoidal]
  (G : D ⥤ E) [G.Additive] [G.PreservesKFlatQuasiIso] [G.PreservesFlat]
  [G.IsLeftAdjoint] [G.Monoidal]
  (H : C ⥤ E) [H.Additive] [H.PreservesKFlatQuasiIso] [H.PreservesFlat]
  [H.IsLeftAdjoint] [H.Monoidal]
private theorem tensor_naturality {K₁ K₂ M₁ M₂ : DerivedCategory C}
    (f : K₁ ⟶ K₂) (g : M₁ ⟶ M₂) :
    F.leftDerivedFunctor.map (f ⊗ₘ g) ≫ (F.leftDerivedTensorComparison.app K₂).app M₂ =
      (F.leftDerivedTensorComparison.app K₁).app M₁ ≫
        (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) := by
  have h₁ := congr_app (F.leftDerivedTensorComparison.naturality f) M₁
  have h₂ := (F.leftDerivedTensorComparison.app K₂).naturality g
  dsimp at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]
set_option maxHeartbeats 1000000 in
-- The proof compares the two natural transformations by their derived counits.
/-- Tensor compatibility descends from the homotopy-category comparison and its counit law.
Source: K-flat derived tensor universal property (blueprint: lem-sf-derived-scalar-tensor).
Proof: use the two-variable derived universal property to test the equation after the
counits. Naturality moves the scalar comparison through the localization tensorator.
Its normalization and the defining counit equations for the three tensor comparisons
reduce both sides to the assumed homotopy-category tensor equation. -/
theorem derivedTensorComparison_of_normalization
    (e : F.mapHomotopyCategory (.up ℤ) ⋙ G.mapHomotopyCategory (.up ℤ) ≅
      H.mapHomotopyCategory (.up ℤ))
    (he : ∀ P Q : HomotopyCategory C (.up ℤ),
      e.hom.app (P ⊗ Q) ≫ OplaxMonoidal.δ (H.mapHomotopyCategory (.up ℤ)) P Q =
        (G.mapHomotopyCategory (.up ℤ)).map
          (OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) P Q) ≫
        OplaxMonoidal.δ (G.mapHomotopyCategory (.up ℤ)) _ _ ≫
          (e.hom.app P ⊗ₘ e.hom.app Q))
    (t : F.leftDerivedFunctor ⋙ G.leftDerivedFunctor ⟶ H.leftDerivedFunctor)
    (ht : ∀ P : HomotopyCategory C (.up ℤ),
      t.app (Qh.obj P) ≫ H.leftDerivedFunctorCounit.app P =
        G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app P) ≫
          G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          Qh.map (e.hom.app P))
    (K M : DerivedCategory C) :
    t.app (K ⊗ M) ≫ (H.leftDerivedTensorComparison.app K).app M =
      G.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
        (G.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) ≫ (t.app K ⊗ₘ t.app M) := by
  let J := F.leftDerivedFunctor ⋙ G.leftDerivedFunctor
  let d : (postcompose₂.obj J).obj (curriedTensor _) ⟶
      (((whiskeringLeft₂ _).obj J).obj J).obj (curriedTensor _) :=
    (postcompose₂.obj G.leftDerivedFunctor).map F.leftDerivedTensorComparison ≫
      (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).map
        G.leftDerivedTensorComparison
  have h : (postcompose₂.map t).app (curriedTensor _) ≫ H.leftDerivedTensorComparison =
      d ≫ (((whiskeringLeft₂ _).map t).app J).app (curriedTensor _) ≫
        (((whiskeringLeft₂ _).obj H.leftDerivedFunctor).map t).app (curriedTensor _) := by
    apply leftDerived₂_ext (H.derivedTensorLeftDerived) (H.derivedTensorLeftDerivedCounit)
      (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    ext P Q
    dsimp [d]
    simp only [Category.assoc]
    rw [H.derivedTensorLeftDerivedCounit_app_app,
      H.leftDerivedTensorComparison_app_app_comp_tensorHom,
      ← tensorHom_def_assoc, tensorHom_comp_tensorHom_assoc, ht, ht,
      ← tensorHom_comp_tensorHom_assoc]
    have n := tensor_naturality G
      (F.leftDerivedFunctorCounit.app P) (F.leftDerivedFunctorCounit.app Q)
    rw [← reassoc_of% n]
    rw [← tensorHom_comp_tensorHom_assoc, LaxMonoidal.μ_natural]
    simp only [Functor.comp_obj]
    rw [G.leftDerivedTensorComparison_app_app_comp_tensorHom_assoc]
    have cF := F.leftDerivedTensorComparison_app_app_comp_tensorHom P Q
    have nG := G.leftDerivedFunctorCounit.naturality
      (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app Q)
    have nt := t.naturality (LaxMonoidal.μ Qh P Q)
    dsimp at nG nt
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, cF,
      Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      reassoc_of% nG, ← reassoc_of% nt, reassoc_of% (ht (P ⊗ Q))]
    simp only [← Qh.map_comp, ← mapHomotopyCategory_δ]
    rw [he]
  have hh := congr_app (congr_app h K) M
  dsimp [d, J] at hh
  simpa only [tensorHom_def, Category.assoc] using hh
end CategoryTheory
