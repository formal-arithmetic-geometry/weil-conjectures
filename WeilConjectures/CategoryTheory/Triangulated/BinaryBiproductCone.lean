/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Cones of morphisms into a binary biproduct

In a pretriangulated category, the cone of a morphism `biprod.lift f g : X ⟶ Y ⊞ Y'` whose
first component `f` is an isomorphism is identified with `Y'`, compatibly with the two
biproduct inclusions. This is used to construct homotopy pushouts of quasi-isomorphisms.

## Main statements

- `CategoryTheory.Pretriangulated.exists_iso_of_distTriang_biprod_lift`
- `CategoryTheory.Pretriangulated.nonempty_iso_obj₁_of_isIso_inl_comp`: dually, the fibre of a
  morphism out of a binary biproduct which is an isomorphism on the first summand is the second
  summand.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasBinaryBiproducts C]

/-- In a distinguished triangle `X ⟶ Y ⊞ Y' ⟶ Z ⟶ X⟦1⟧` whose first morphism is
`biprod.lift f g` with `f` an isomorphism, there is an isomorphism `θ : Z ≅ Y'` such that
`biprod.inr ≫ ψ ≫ θ.hom = 𝟙 Y'` and `biprod.inl ≫ ψ ≫ θ.hom = -(f⁻¹ ≫ g)`. -/
theorem exists_iso_of_distTriang_biprod_lift {X Y Y' Z : C} (f : X ⟶ Y) (g : X ⟶ Y')
    (ψ : Y ⊞ Y' ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift f g) ψ δ ∈ distTriang C) [IsIso f] :
    ∃ θ : Z ≅ Y', biprod.inr ≫ ψ ≫ θ.hom = 𝟙 Y' ∧
      biprod.inl ≫ ψ ≫ θ.hom = -(inv f ≫ g) := by
  let E : Y ⊞ Y' ≅ Y ⊞ Y' :=
    { hom := biprod.desc (biprod.lift (𝟙 Y) (-(inv f ≫ g))) biprod.inr
      inv := biprod.desc (biprod.lift (𝟙 Y) (inv f ≫ g)) biprod.inr
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  have hT' : Triangle.mk (biprod.lift f 0) (E.inv ≫ ψ) δ ∈ distTriang C :=
    isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) E.symm (Iso.refl _)
      (by apply biprod.hom_ext <;> simp [E]) (by simp) (by simp))
  have hT'' : Triangle.mk (biprod.lift f 0) (biprod.snd : Y ⊞ Y' ⟶ Y') 0 ∈ distTriang C :=
    isomorphic_distinguished _ (binaryBiproductTriangle_distinguished X Y') _
      (Triangle.isoMk _ _ (Iso.refl _) (biprod.mapIso (asIso f).symm (Iso.refl _)) (Iso.refl _)
        (by apply biprod.hom_ext <;> simp) (by apply biprod.hom_ext' <;> simp) (by simp))
  let e := isoTriangleOfIso₁₂ _ _ hT' hT'' (Iso.refl _) (Iso.refl _) (by simp)
  have h₂ : E.inv ≫ ψ ≫ e.hom.hom₃ = biprod.snd := by
    have := e.hom.comm₂
    simp only [e, isoTriangleOfIso₁₂_hom_hom₂] at this
    simpa [e] using this
  refine ⟨Triangle.π₃.mapIso e, ?_, ?_⟩
  · have : biprod.inr ≫ E.inv = (biprod.inr : Y' ⟶ Y ⊞ Y') := by simp [E]
    simp only [Functor.mapIso_hom, Triangle.π₃_map]
    rw [← this, assoc, h₂, biprod.inr_snd]
  · have : biprod.inl ≫ E.hom ≫ E.inv = (biprod.inl : Y ⟶ Y ⊞ Y') := by simp
    simp only [Functor.mapIso_hom, Triangle.π₃_map]
    rw [← this, assoc, assoc, h₂]
    simp [E]

/-- Let `T = (X, Y, Z)` be a distinguished triangle and `D : M ⊞ N ≅ Y` an isomorphism such that
`M ⟶ M ⊞ N ⟶ Y ⟶ Z` is an isomorphism. Then `X ≅ N`. -/
lemma nonempty_iso_obj₁_of_isIso_inl_comp {T : Triangle C} (hT : T ∈ distTriang C) {M N : C}
    (D : M ⊞ N ⟶ T.obj₂) [IsIso D] (h : IsIso (biprod.inl ≫ D ≫ T.mor₂)) :
    Nonempty (N ≅ T.obj₁) := by
  set φ := biprod.inl ≫ D ≫ T.mor₂
  set ψ : N ⟶ M := biprod.inr ≫ D ≫ T.mor₂ ≫ inv φ
  -- the shear automorphism `M ⊞ N ≅ N ⊞ M`, making the composite to `Z` vanish on `N`
  let f : N ⊞ M ⟶ M ⊞ N := biprod.desc (biprod.inr - ψ ≫ biprod.inl) biprod.inl
  let g : M ⊞ N ⟶ N ⊞ M := biprod.desc biprod.inr (biprod.inl + ψ ≫ biprod.inr)
  have : IsIso f := ⟨g, by ext <;> simp [f, g], by ext <;> simp [f, g]⟩
  have hσ : ((biprod.inr - ψ ≫ biprod.inl) ≫ D) ≫ T.mor₂ = 0 := by
    have : biprod.inl ≫ D ≫ T.mor₂ = φ := rfl
    simp only [Preadditive.sub_comp, Category.assoc, this, ψ, IsIso.inv_hom_id,
      Category.comp_id, sub_self]
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ T hT _ hσ
  let τ : binaryBiproductTriangle N M ⟶ T :=
    { hom₁ := a
      hom₂ := f ≫ D
      hom₃ := φ
      comm₁ := by simp [f, ← ha]
      comm₂ := by
        refine biprod.hom_ext' _ _ ?_ ?_
        · simpa [f, Category.assoc] using hσ.symm
        · simp [f, φ]
      comm₃ := by simp [φ, comp_distTriang_mor_zero₂₃ _ hT] }
  have : IsIso τ.hom₁ := isIso₁_of_isIso₂₃ τ (binaryBiproductTriangle_distinguished N M) hT
    (by dsimp [τ]; infer_instance) (by dsimp [τ]; infer_instance)
  exact ⟨asIso τ.hom₁⟩


end CategoryTheory.Pretriangulated
