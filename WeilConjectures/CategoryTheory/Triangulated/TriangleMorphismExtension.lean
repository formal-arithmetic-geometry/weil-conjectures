/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Extending a morphism of middle terms to a morphism of distinguished triangles

Let `T = (X, Y, Z, u, v, d)` and `T' = (X', Y', Z', u', v', d')` be distinguished triangles in
a pretriangulated category and `g : Y ⟶ Y'`. We show [BBD, Prop. 1.1.9, Cor. 1.1.10]:

* `CategoryTheory.Pretriangulated.tfae_exists_triangleHom`: the conditions `v' g u = 0`,
  "there is `f` with `u' f = g u`", "there is `h` with `h v = v' g`" and "`g` is the middle
  component of a morphism of triangles" are equivalent;
* if `Hom(X⟦1⟧, Z') = 0`, then `f` and `h` are unique, and any `f`, `h` making the first two
  squares commute make the third one commute
  (`CategoryTheory.Pretriangulated.comm₃_of_subsingleton`);
* if `Hom(X⟦1⟧, Z) = 0`, the third morphism of `T` is the only morphism completing `u`, `v`
  to a distinguished triangle (`CategoryTheory.Pretriangulated.mor₃_unique_of_subsingleton`).

The Mathlib inputs are the exactness of `Hom(W, -)` and `Hom(-, W)` on distinguished triangles
(`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`,
`CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`; blueprint
`lem-weil-pbc-hom-into-triangle-exact`, `lem-weil-pbc-hom-out-of-triangle-exact`) and the
axiom TR3 in its two forms
(`CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism` and
`CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁`; blueprint
`lem-weil-pbc-tr3-second-square`).
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)

include hT hT'

/-- This is blueprint `lem-weil-pbc-triangle-morphism-extension` (1) [BBD, Prop. 1.1.9]. For
distinguished triangles `T`, `T'` and `g : T.obj₂ ⟶ T'.obj₂`, the following are equivalent:
(a) `T.mor₁ ≫ g ≫ T'.mor₂ = 0`; (b) `g` extends to the first square; (b') `g` extends to the
second square; (c) `g` is the middle component of a morphism of triangles `T ⟶ T'`. -/
theorem tfae_exists_triangleHom (g : T.obj₂ ⟶ T'.obj₂) :
    List.TFAE [T.mor₁ ≫ g ≫ T'.mor₂ = 0,
      ∃ f : T.obj₁ ⟶ T'.obj₁, T.mor₁ ≫ g = f ≫ T'.mor₁,
      ∃ h : T.obj₃ ⟶ T'.obj₃, T.mor₂ ≫ h = g ≫ T'.mor₂,
      ∃ τ : T ⟶ T', τ.hom₂ = g] := by
  tfae_have 1 → 4 := exists_triangleHom_of_comp_eq_zero hT hT' g
  tfae_have 4 → 2 := by
    rintro ⟨τ, rfl⟩
    exact ⟨τ.hom₁, τ.comm₁⟩
  tfae_have 4 → 3 := by
    rintro ⟨τ, rfl⟩
    exact ⟨τ.hom₃, τ.comm₂⟩
  tfae_have 2 → 1 := by
    rintro ⟨f, hf⟩
    rw [← assoc, hf, assoc, comp_distTriang_mor_zero₁₂ _ hT', comp_zero]
  tfae_have 3 → 1 := by
    rintro ⟨h, hh⟩
    rw [← hh, ← assoc, comp_distTriang_mor_zero₁₂ _ hT, zero_comp]
  tfae_finish

variable [Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃)]

omit hT in
/-- This is blueprint `lem-weil-pbc-triangle-morphism-extension` (2), uniqueness of the first
component: if `Hom(T.obj₁⟦1⟧, T'.obj₃) = 0`, a morphism `f : T.obj₁ ⟶ T'.obj₁` is determined
by `f ≫ T'.mor₁`. -/
theorem hom₁_unique_of_subsingleton {f f' : T.obj₁ ⟶ T'.obj₁}
    (h : f ≫ T'.mor₁ = f' ≫ T'.mor₁) : f = f' :=
  Triangle.cancel_mor₁_of_subsingleton hT' h

omit hT' in
/-- This is blueprint `lem-weil-pbc-triangle-morphism-extension` (2), uniqueness of the third
component: if `Hom(T.obj₁⟦1⟧, T'.obj₃) = 0`, a morphism `h : T.obj₃ ⟶ T'.obj₃` is determined
by `T.mor₂ ≫ h`. -/
theorem hom₃_unique_of_subsingleton {h h' : T.obj₃ ⟶ T'.obj₃}
    (H : T.mor₂ ≫ h = T.mor₂ ≫ h') : h = h' :=
  Triangle.cancel_mor₂_of_subsingleton hT H

/-- This is blueprint `lem-weil-pbc-triangle-morphism-extension` (2): if
`Hom(T.obj₁⟦1⟧, T'.obj₃) = 0`, then any `f`, `g`, `h` making the first two squares commute
also make the third square commute, i.e. they form a morphism of triangles. -/
theorem comm₃_of_subsingleton (f : T.obj₁ ⟶ T'.obj₁) (g : T.obj₂ ⟶ T'.obj₂)
    (h : T.obj₃ ⟶ T'.obj₃) (hf : T.mor₁ ≫ g = f ≫ T'.mor₁) (hh : T.mor₂ ≫ h = g ≫ T'.mor₂) :
    T.mor₃ ≫ f⟦(1 : ℤ)⟧' = h ≫ T'.mor₃ := by
  obtain ⟨h₀, hh₀, hh₀'⟩ := complete_distinguished_triangle_morphism T T' hT hT' f g hf
  obtain rfl : h₀ = h := hom₃_unique_of_subsingleton hT (by rw [hh₀, hh])
  exact hh₀'

/-- The morphism of triangles `T ⟶ T'` with given components `f`, `g`, `h` making the first two
squares commute, when `Hom(T.obj₁⟦1⟧, T'.obj₃) = 0` (blueprint
`lem-weil-pbc-triangle-morphism-extension` (2)). -/
@[simps]
def triangleHomOfSubsingleton (f : T.obj₁ ⟶ T'.obj₁) (g : T.obj₂ ⟶ T'.obj₂)
    (h : T.obj₃ ⟶ T'.obj₃) (hf : T.mor₁ ≫ g = f ≫ T'.mor₁) (hh : T.mor₂ ≫ h = g ≫ T'.mor₂) :
    T ⟶ T' where
  hom₁ := f
  hom₂ := g
  hom₃ := h
  comm₁ := hf
  comm₂ := hh
  comm₃ := comm₃_of_subsingleton hT hT' f g h hf hh

omit hT'

/-- This is blueprint `lem-weil-pbc-triangle-morphism-extension` (3) [BBD, Cor. 1.1.10 (ii)]:
if `Hom(T.obj₁⟦1⟧, T.obj₃) = 0`, the third morphism of a distinguished triangle `T` is the
only morphism `x` such that `T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁⟦1⟧` with third arrow `x` is
distinguished. -/
theorem mor₃_unique_of_subsingleton [Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T.obj₃)]
    (x : T.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧) (hx : Triangle.mk T.mor₁ T.mor₂ x ∈ distTriang C) :
    x = T.mor₃ := by
  have : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ (Triangle.mk T.mor₁ T.mor₂ x).obj₃) := ‹_›
  have := comm₃_of_subsingleton hT hx (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp)
  simpa using this.symm

end CategoryTheory.Pretriangulated
