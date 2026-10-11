/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Objects on which a scalar acts invertibly, and the shift on a countable product

Let `C` be a pretriangulated category which is linear over a commutative ring `R`, with
`R`-linear shift functors, and let `ϖ ∈ R`. This file characterises the objects `K` of `C`
which receive no nonzero morphism from an object on which `ϖ` acts invertibly (the right
orthogonal of `CategoryTheory.smulInvertible C ϖ`): given a product `∏ₙ K` of countably many
copies of `K`, with shift endomorphism `s` (the components of `s` are the projections
`∏ₙ K ⟶ K` of index `n + 1`), this holds exactly when

```
  1 - ϖ • s : ∏ₙ K ⟶ ∏ₙ K
```

is an isomorphism (`CategoryTheory.Pretriangulated.rightOrthogonal_smulInvertible_iff`). The
mapping cone of `1 - ϖ • s` is the shifted homotopy limit `R lim (⋯ ─ϖ→ K ─ϖ→ K)⟦1⟧`, so this
is the characterisation of derived completeness by the vanishing of `R lim (⋯ ─ϖ→ K ─ϖ→ K)`
(Stacks, Tag 091Q).

The key point is that `ϖ` acts invertibly on the mapping cone `Z` of any morphism of the form
`1 - ϖ • s` (`CategoryTheory.Pretriangulated.isIso_smul_id_of_distTriang`): `s` induces an
endomorphism `σ` of `Z`, and `ϖ • σ - 1` vanishes on the two morphisms of the triangle which
touch `Z`, so its square is zero.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated Preadditive

namespace CategoryTheory

variable {R : Type*} [CommRing R] {C : Type*} [Category C]

namespace Pretriangulated

/-- The shift endomorphism `s` of a product `∏ₙ K` of countably many copies of `K`: its
component of index `n` is the projection of index `n + 1`. -/
noncomputable def fanShift {K : C} {P : Fan fun _ : ℕ ↦ K} (hP : IsLimit P) : P.pt ⟶ P.pt :=
  Fan.IsLimit.lift hP fun n ↦ P.proj (n + 1)

@[reassoc (attr := simp)]
lemma fanShift_proj {K : C} {P : Fan fun _ : ℕ ↦ K} (hP : IsLimit P) (n : ℕ) :
    fanShift hP ≫ P.proj n = P.proj (n + 1) :=
  Fan.IsLimit.fac hP _ n

end Pretriangulated

variable [Preadditive C] [Linear R C]

variable (C) in
/-- The objects of an `R`-linear category on which `ϖ ∈ R` acts invertibly. -/
def smulInvertible (ϖ : R) : ObjectProperty C :=
  fun X ↦ IsIso (ϖ • 𝟙 X)

lemma smulInvertible_iff (ϖ : R) (X : C) : smulInvertible C ϖ X ↔ IsIso (ϖ • 𝟙 X) :=
  Iff.rfl

instance (ϖ : R) {A : Type*} [AddMonoid A] [HasShift C A]
    [∀ a : A, (shiftFunctor C a).Linear R] (a : A) :
    (smulInvertible C ϖ).IsStableUnderShiftBy a where
  le_shift X (hX : IsIso (ϖ • 𝟙 X)) := by
    change IsIso (ϖ • 𝟙 (X⟦a⟧))
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance

instance (ϖ : R) {A : Type*} [AddMonoid A] [HasShift C A]
    [∀ a : A, (shiftFunctor C a).Linear R] :
    (smulInvertible C ϖ).IsStableUnderShift A where

namespace Pretriangulated

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]

/-- If `T : P ⟶ P ⟶ Z ⟶ P⟦1⟧` is a distinguished triangle whose first morphism is
`1 - ϖ • s`, then `ϖ` acts invertibly on `Z`. -/
lemma isIso_smul_id_of_distTriang {P Z : C} (ϖ : R) (s : P ⟶ P) (g : P ⟶ Z)
    (h : Z ⟶ P⟦(1 : ℤ)⟧) (hT : Triangle.mk (𝟙 P - ϖ • s) g h ∈ distTriang C) :
    IsIso (ϖ • 𝟙 Z) := by
  obtain ⟨(σ : Z ⟶ Z), hσ₁, hσ₂⟩ := complete_distinguished_triangle_morphism _ _ hT hT s s (by
    change (𝟙 P - ϖ • s) ≫ s = s ≫ (𝟙 P - ϖ • s)
    simp only [sub_comp, comp_sub, id_comp, comp_id, Linear.smul_comp, Linear.comp_smul])
  change g ≫ σ = s ≫ g at hσ₁
  change h ≫ s⟦(1 : ℤ)⟧' = σ ≫ h at hσ₂
  have hgh : g ≫ h = 0 := comp_distTriang_mor_zero₂₃ _ hT
  have hφg : (𝟙 P - ϖ • s) ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hhφ : h ≫ (𝟙 P - ϖ • s)⟦(1 : ℤ)⟧' = 0 := by
    have := comp_distTriang_mor_zero₃₁ _ hT
    change h ≫ (𝟙 P - ϖ • s)⟦(1 : ℤ)⟧' = 0 at this
    exact this
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Z ⟶ Z, ψ = ϖ • σ - 𝟙 Z := ⟨_, rfl⟩
  have h₁ : g ≫ ψ = 0 := by
    simp only [hψdef, comp_sub, Linear.comp_smul, hσ₁, comp_id]
    rw [← Linear.smul_comp, ← sub_eq_zero.mpr rfl]
    have : (ϖ • s) ≫ g = g := by
      have := hφg
      rw [sub_comp, id_comp, sub_eq_zero] at this
      exact this.symm
    rw [this, sub_self]
  have h₂ : ψ ≫ h = 0 := by
    simp only [hψdef, sub_comp, Linear.smul_comp, ← hσ₂, id_comp]
    have : h ≫ (ϖ • s)⟦(1 : ℤ)⟧' = h := by
      rw [Functor.map_sub, CategoryTheory.Functor.map_id, comp_sub, comp_id, sub_eq_zero]
        at hhφ
      exact hhφ.symm
    rw [← Linear.comp_smul, ← Functor.map_smul, this, sub_self]
  obtain ⟨(k : P⟦(1 : ℤ)⟧ ⟶ Z), hk⟩ := Triangle.yoneda_exact₃ _ hT ψ h₁
  obtain ⟨(l : Z ⟶ P), hl⟩ := Triangle.coyoneda_exact₃ _ hT ψ h₂
  change ψ = h ≫ k at hk
  change ψ = l ≫ g at hl
  have hψ : ψ ≫ ψ = 0 := by
    rw [show ψ ≫ ψ = (l ≫ g) ≫ (h ≫ k) by rw [← hl, ← hk]]
    rw [assoc, reassoc_of% hgh, zero_comp, comp_zero]
  have hσψ : ϖ • σ = 𝟙 Z + ψ := by rw [hψdef]; abel
  have e : (ϖ • 𝟙 Z) ≫ σ ≫ (𝟙 Z - ψ) = 𝟙 Z := by
    rw [← assoc, Linear.smul_comp, id_comp, hσψ, add_comp, id_comp, comp_sub, comp_id, hψ]
    abel
  refine ⟨σ ≫ (𝟙 Z - ψ), e, ?_⟩
  rw [show (σ ≫ (𝟙 Z - ψ)) ≫ (ϖ • 𝟙 Z) = (ϖ • 𝟙 Z) ≫ σ ≫ (𝟙 Z - ψ) by
    rw [Linear.comp_smul, Linear.smul_comp, comp_id, id_comp], e]

/-- An object `K` receives no nonzero morphism from an object on which `ϖ` acts invertibly if
and only if `1 - ϖ • s` is an isomorphism, where `s` is the shift endomorphism of a product
`∏ₙ K` of countably many copies of `K`. -/
theorem rightOrthogonal_smulInvertible_iff (ϖ : R) {K : C} {P : Fan fun _ : ℕ ↦ K}
    (hP : IsLimit P) :
    (smulInvertible C ϖ).rightOrthogonal K ↔ IsIso (𝟙 P.pt - ϖ • fanShift hP) := by
  constructor
  · intro hK
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (𝟙 P.pt - ϖ • fanShift hP)
    have hZ : IsIso (ϖ • 𝟙 Z) := isIso_smul_id_of_distTriang ϖ _ g h hT
    have hPorth : (smulInvertible C ϖ).rightOrthogonal P.pt := fun X f hX ↦
      Fan.IsLimit.hom_ext hP _ _ fun n ↦ by rw [zero_comp]; exact hK _ hX
    have hZorth : (smulInvertible C ϖ).rightOrthogonal Z :=
      (smulInvertible C ϖ).rightOrthogonal.ext_of_isTriangulatedClosed₃ _ hT hPorth hPorth
    have hZero : IsZero Z := by
      rw [IsZero.iff_id_eq_zero]
      exact hZorth (𝟙 Z) hZ
    exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZero
  · intro hφ X f (hX : IsIso (ϖ • 𝟙 X))
    let u : X ⟶ X := inv (ϖ • 𝟙 X)
    have hu : ∀ {Y : C} (a : X ⟶ Y), ϖ • (u ≫ a) = a := fun a ↦ by
      rw [← Linear.smul_comp, show ϖ • u = (ϖ • 𝟙 X) ≫ u by rw [Linear.smul_comp, id_comp],
        IsIso.hom_inv_id, id_comp]
    let v : ℕ → (X ⟶ X) := fun n ↦ Nat.rec (𝟙 X) (fun _ w ↦ u ≫ w) n
    let a : X ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦ v n ≫ f
    have ha : a ≫ (𝟙 P.pt - ϖ • fanShift hP) = 0 :=
      Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
        simp only [comp_sub, comp_id, Linear.comp_smul, sub_comp, Linear.smul_comp, assoc,
          fanShift_proj, zero_comp, a, Fan.IsLimit.fac]
        change v n ≫ f - ϖ • ((u ≫ v n) ≫ f) = 0
        rw [assoc, hu, sub_self]
    have ha0 : a = 0 := by
      rw [← cancel_mono (𝟙 P.pt - ϖ • fanShift hP), ha, zero_comp]
    have := Fan.IsLimit.fac hP (fun n ↦ v n ≫ f) 0
    change a ≫ P.proj 0 = 𝟙 X ≫ f at this
    rw [ha0, zero_comp, id_comp] at this
    exact this.symm

end Pretriangulated

end CategoryTheory
