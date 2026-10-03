/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Morphisms of distinguished triangles with a given middle component

Let `T = (X, Y, Z)` and `T' = (X', Y', Z')` be distinguished triangles in a pretriangulated
category. A morphism `φ : Y ⟶ Y'` with `X ⟶ Y ⟶ Y' ⟶ Z'` zero extends to a morphism of triangles
`T ⟶ T'`, and if `Hom(X⟦1⟧, Z') = 0` this extension is unique [BBD, 1.1.9].

## Main statements

- `CategoryTheory.Pretriangulated.exists_triangleHom_of_comp_eq_zero`: existence of the
  extension.
- `CategoryTheory.Pretriangulated.triangleHom_ext_of_subsingleton`: uniqueness of the
  extension.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

namespace Pretriangulated

namespace Triangle

variable {T : Triangle C} (hT : T ∈ distTriang C)
include hT

/-- If `Hom(X⟦1⟧, T.obj₃) = 0`, two maps `X ⟶ T.obj₁` with the same composite with `T.mor₁`
are equal. -/
lemma cancel_mor₁_of_subsingleton {X : C} [Subsingleton (X⟦(1 : ℤ)⟧ ⟶ T.obj₃)]
    {a a' : X ⟶ T.obj₁} (h : a ≫ T.mor₁ = a' ≫ T.mor₁) : a = a' := by
  rw [← sub_eq_zero]
  obtain ⟨g, hg⟩ := coyoneda_exact₁ T hT ((a - a')⟦(1 : ℤ)⟧')
    (by rw [← Functor.map_comp, Preadditive.sub_comp, h, sub_self, Functor.map_zero])
  rw [Subsingleton.elim g 0, zero_comp] at hg
  exact (CategoryTheory.shiftFunctor C (1 : ℤ)).map_eq_zero_iff.mp hg

/-- If `Hom(T.obj₁⟦1⟧, Y) = 0`, two maps `T.obj₃ ⟶ Y` with the same composite with `T.mor₂`
are equal. -/
lemma cancel_mor₂_of_subsingleton {Y : C} [Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ Y)]
    {c c' : T.obj₃ ⟶ Y} (h : T.mor₂ ≫ c = T.mor₂ ≫ c') : c = c' := by
  rw [← sub_eq_zero]
  obtain ⟨g, hg⟩ := yoneda_exact₃ T hT (c - c') (by rw [Preadditive.comp_sub, h, sub_self])
  rw [hg, Subsingleton.elim g 0, comp_zero]

end Triangle

/-- **Extension of a middle component** [BBD, 1.1.9]. Given distinguished triangles `T` and `T'`,
a morphism `φ : T.obj₂ ⟶ T'.obj₂` such that `T.mor₁ ≫ φ ≫ T'.mor₂ = 0` is the middle component of
a morphism of triangles `T ⟶ T'`. -/
theorem exists_triangleHom_of_comp_eq_zero {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) (φ : T.obj₂ ⟶ T'.obj₂) (hφ : T.mor₁ ≫ φ ≫ T'.mor₂ = 0) :
    ∃ τ : T ⟶ T', τ.hom₂ = φ := by
  obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ T' hT' (T.mor₁ ≫ φ) (by simpa using hφ)
  obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism T T' hT hT' a φ ha
  exact ⟨{ hom₁ := a, hom₂ := φ, hom₃ := c, comm₁ := ha, comm₂ := hc₁, comm₃ := hc₂ }, rfl⟩

/-- **Uniqueness of the extension of a middle component** [BBD, 1.1.9]. Let `T` and `T'` be
distinguished triangles with `Hom(T.obj₁⟦1⟧, T'.obj₃) = 0`. Then a morphism of triangles
`T ⟶ T'` is determined by its middle component. -/
theorem triangleHom_ext_of_subsingleton {T T' : Triangle C} (hT : T ∈ distTriang C)
    (hT' : T' ∈ distTriang C) [Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃)] {τ τ' : T ⟶ T'}
    (h : τ.hom₂ = τ'.hom₂) : τ = τ' := by
  ext
  · exact Triangle.cancel_mor₁_of_subsingleton hT' (by rw [← τ.comm₁, ← τ'.comm₁, h])
  · exact h
  · exact Triangle.cancel_mor₂_of_subsingleton hT (by rw [τ.comm₂, τ'.comm₂, h])

end Pretriangulated

end CategoryTheory
