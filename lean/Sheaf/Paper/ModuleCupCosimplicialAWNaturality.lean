/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.ModuleCupGodementCosimplicialInput
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Sheaf.Paper.ModuleCupAWLeibniz

/-! # Naturality of the Alexander--Whitney pairing -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Functorial action of the alternating coface complex extended by zero.
Source: Stacks Project, Tag 0FKR.
(blueprint: lem-sc-module-cup-cosimplicial-aw-natural). -/
def moduleCup_cosimplicialMap (X : Scheme.{u})
    {A B : CosimplicialObject X.Modules} (f : A ⟶ B) :
    moduleCup_cosimplicialComplex X A ⟶ moduleCup_cosimplicialComplex X B :=
  HomologicalComplex.extendMap ((alternatingCofaceMapComplex X.Modules).map f)
    ComplexShape.embeddingUpNat

private theorem map_f (X : Scheme.{u})
    {A B : CosimplicialObject X.Modules} (f : A ⟶ B)
    (i : ℕ) (n : ℤ) (h : (i : ℤ) = n) :
    (moduleCup_cosimplicialMap X f).f n =
      (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
        ComplexShape.embeddingUpNat h).hom ≫ f.app ⦋i⦌ ≫
      (((alternatingCofaceMapComplex X.Modules).obj B).extendXIso
        ComplexShape.embeddingUpNat h).inv := by
  exact HomologicalComplex.extendMap_f _ _ h

private theorem summand_natural (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C A₁ B₁ C₁ : CosimplicialObject X.Modules)
    (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
    (μ₁ : moduleCup_cosimplicialTensor X A₁ B₁ ⟶ C₁)
    (f : A ⟶ A₁) (g : B ⟶ B₁) (k : C ⟶ C₁)
    (hμ : ∀ n : SimplexCategory,
      μ.app n ≫ k.app n = (f.app n ⊗ₘ g.app n) ≫ μ₁.app n)
    (r s n : ℤ) (h : r + s = n) :
    moduleCup_awSummand X A B C μ r s n h ≫
        (moduleCup_cosimplicialMap X k).f n =
      ((moduleCup_cosimplicialMap X f).f r ⊗ₘ
        (moduleCup_cosimplicialMap X g).f s) ≫
        moduleCup_awSummand X A₁ B₁ C₁ μ₁ r s n h := by
  by_cases hr : 0 ≤ r
  · by_cases hs : 0 ≤ s
    · rw [moduleCup_awSummand, dif_pos hr, dif_pos hs,
        moduleCup_awSummand, dif_pos hr, dif_pos hs,
        map_f X k (r.toNat + s.toNat) n (by
          rw [Nat.cast_add, Int.toNat_of_nonneg hr, Int.toNat_of_nonneg hs, h]),
        map_f X f r.toNat r (Int.toNat_of_nonneg hr),
        map_f X g s.toNat s (Int.toNat_of_nonneg hs)]
      dsimp only [moduleCup_cosimplicialComplex, CosimplicialObject] at *
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      erw [← Category.assoc (μ.app _) (k.app _), hμ]
      simp only [tensorHom_comp_tensorHom_assoc, Category.assoc,
        Iso.inv_hom_id_assoc]
      rw [f.naturality, g.naturality]
    · simp [moduleCup_awSummand, hr, hs]
  · simp [moduleCup_awSummand, hr]

private theorem aw_components (X : Scheme.{u}) [MonoidalPreadditive X.Modules]
    (A B C : CosimplicialObject X.Modules)
    (μ : moduleCup_cosimplicialTensor X A B ⟶ C) :
    ∃ t : HomologicalComplex.tensorObj (moduleCup_cosimplicialComplex X A)
        (moduleCup_cosimplicialComplex X B) ⟶ moduleCup_cosimplicialComplex X C,
      ∀ n : ℤ, t.f n = moduleCup_awComponent X A B C μ n := by
  let t : HomologicalComplex.tensorObj (moduleCup_cosimplicialComplex X A)
      (moduleCup_cosimplicialComplex X B) ⟶ moduleCup_cosimplicialComplex X C :=
    CochainComplex.ofHom (moduleCup_awComponent X A B C μ) (by
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro r s h
      have h' : r + s = n := h
      by_cases hr : 0 ≤ r
      · by_cases hs : 0 ≤ s
        · rw [moduleCup_ι_awComponent_assoc, ← Category.assoc]
          rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
            HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
            HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
              (rfl : (ComplexShape.up ℤ).Rel r (r + 1)) _ _
              (show r + 1 + s = n + 1 by omega),
            HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
              (rfl : (ComplexShape.up ℤ).Rel s (s + 1)) _
              (show r + (s + 1) = n + 1 by omega)]
          simp only [curriedTensor_obj_obj, ComplexShape.ε₁_def, curriedTensor_map_app,
            one_smul, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ, curriedTensor_obj_map,
            Preadditive.add_comp, Category.assoc, Linear.units_smul_comp]
          rw [moduleCup_ι_awComponent, moduleCup_ι_awComponent]
          exact moduleCup_awSummand_leibniz X A B C μ r s n h' hr hs
        · have hz : IsZero ((moduleCup_cosimplicialComplex X B).X s) := by
            apply HomologicalComplex.isZero_extend_X
            intro i hi
            change (i : ℤ) = s at hi
            omega
          exact (((curriedTensor X.Modules).obj _).map_isZero hz).eq_of_src _ _
      · have hz : IsZero ((moduleCup_cosimplicialComplex X A).X r) := by
          apply HomologicalComplex.isZero_extend_X
          intro i hi
          change (i : ℤ) = r at hi
          omega
        exact (((curriedTensor X.Modules).map_isZero hz).obj _).eq_of_src _ _)
  exact ⟨t, fun _ ↦ rfl⟩

/-- Alexander--Whitney maps for compatible cosimplicial pairings can be chosen naturally.
Source: Banerjee, Tensor Structure on Smooth Motives, §1.1.4, p. 16, the front/back formula.
(blueprint: lem-sc-module-cup-cosimplicial-aw-natural)
Proof: use the explicit front/back components for both maps. The Leibniz identity gives
cochain maps. On each tensor summand, the coefficient transformations commute with both
front/back simplex inclusions. The assumed degreewise pairing square then gives the desired
square; the coproduct inclusions detect equality. In bidegree (0,0), both inclusions are
identities, yielding the two zero-degree equations. Negative summands vanish. -/
theorem moduleCup_cosimplicial_aw_natural (X : Scheme.{u})
    [MonoidalPreadditive X.Modules]
    (A B C A₁ B₁ C₁ : CosimplicialObject X.Modules)
    (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
    (μ₁ : moduleCup_cosimplicialTensor X A₁ B₁ ⟶ C₁)
    (f : A ⟶ A₁) (g : B ⟶ B₁) (k : C ⟶ C₁)
    (hμ : ∀ n : SimplexCategory,
      μ.app n ≫ k.app n = (f.app n ⊗ₘ g.app n) ≫ μ₁.app n) :
    ∃ (t : HomologicalComplex.tensorObj (moduleCup_cosimplicialComplex X A)
        (moduleCup_cosimplicialComplex X B) ⟶ moduleCup_cosimplicialComplex X C)
      (t₁ : HomologicalComplex.tensorObj (moduleCup_cosimplicialComplex X A₁)
        (moduleCup_cosimplicialComplex X B₁) ⟶ moduleCup_cosimplicialComplex X C₁),
      HomologicalComplex.ιTensorObj (moduleCup_cosimplicialComplex X A)
          (moduleCup_cosimplicialComplex X B) 0 0 0 (by simp) ≫ t.f 0 =
        moduleCup_cosimplicialZeroPair X A B C μ ∧
      HomologicalComplex.ιTensorObj (moduleCup_cosimplicialComplex X A₁)
          (moduleCup_cosimplicialComplex X B₁) 0 0 0 (by simp) ≫ t₁.f 0 =
        moduleCup_cosimplicialZeroPair X A₁ B₁ C₁ μ₁ ∧
      t ≫ moduleCup_cosimplicialMap X k =
        HomologicalComplex.tensorHom (moduleCup_cosimplicialMap X f)
          (moduleCup_cosimplicialMap X g) ≫ t₁ := by
  obtain ⟨t, ht⟩ := aw_components X A B C μ
  obtain ⟨t₁, ht₁⟩ := aw_components X A₁ B₁ C₁ μ₁
  refine ⟨t, t₁, ?_, ?_, ?_⟩
  · rw [ht, moduleCup_ι_awComponent, moduleCup_awSummand_zero]
  · rw [ht₁, moduleCup_ι_awComponent, moduleCup_awSummand_zero]
  · apply HomologicalComplex.hom_ext
    intro n
    dsimp only [HomologicalComplex.comp_f]
    rw [ht, ht₁]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro r s h
    rw [moduleCup_ι_awComponent_assoc, ← Category.assoc,
      HomologicalComplex.ι_mapBifunctorMap]
    change _ = ((moduleCup_cosimplicialMap X f).f r ⊗ₘ
      (moduleCup_cosimplicialMap X g).f s) ≫ _ ≫ _
    rw [moduleCup_ι_awComponent]
    exact summand_natural X A B C A₁ B₁ C₁ μ μ₁ f g k hμ r s n h

end
end AlgebraicGeometry.Scheme.Modules
