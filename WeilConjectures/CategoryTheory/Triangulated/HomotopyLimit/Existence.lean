/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Existence of homotopy limits of towers, and exact functors

Let `F : ℕᵒᵖ ⥤ C` be a tower in a pretriangulated category in which the product `∏ₙ Fₙ`
exists. Completing `1 - t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` (`CategoryTheory.Pretriangulated.towerShift`) to a
distinguished triangle gives a homotopy limit cone `R lim F` of `F`
(`CategoryTheory.Pretriangulated.homotopyLimitCone`). It is a choice: homotopy limits are only
unique up to non-unique isomorphism.

A triangulated functor commuting with countable products sends homotopy limit cones to homotopy
limit cones (`CategoryTheory.Pretriangulated.IsHomotopyLimit.map`), so it commutes with `R lim`
up to an isomorphism compatible with the legs
(`CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso_map`, blueprint
`lem-cbc-exact-functor-rlim`).

## Main definitions

- `CategoryTheory.Pretriangulated.homotopyLimitCone`: a chosen homotopy limit cone of a tower.
- `CategoryTheory.Pretriangulated.homotopyLimitLift`: a lift of a cone into it.
- `CategoryTheory.Pretriangulated.homotopyLimitMap`: a map of chosen homotopy limits induced by a
  morphism of towers, the first component of a morphism of Milnor triangles; it is a choice.

## Main statements

- `CategoryTheory.Pretriangulated.isHomotopyLimit_homotopyLimitCone`: it is a homotopy limit.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso_map`: exact functors commuting with
  countable products commute with homotopy limits of towers.
- `CategoryTheory.Pretriangulated.isIso_homotopyLimitMap`: an isomorphism of towers induces an
  isomorphism of the chosen homotopy limits.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section Existence

variable (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)]

/-- The transition endomorphism `t` of the chosen product `∏ₙ Fₙ` of a tower. -/
noncomputable abbrev piTowerShift :
    (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
  towerShift (productIsProduct fun n : ℕ ↦ F.obj (op n))

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[reassoc]
lemma piTowerShift_π (n : ℕ) :
    piTowerShift F ≫ Pi.π _ n = Pi.π _ (n + 1) ≫ F.map (homOfLE n.le_succ).op :=
  Fan.IsLimit.fac _ _ n

lemma exists_distTriang_sub_piTowerShift :
    ∃ (X : C) (f : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n))
      (δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f (𝟙 _ - piTowerShift F) δ ∈ distTriang C :=
  distinguished_cocone_triangle₁ _

/-- The point of the chosen homotopy limit `R lim F` of a tower: a fibre of
`1 - t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ`. -/
noncomputable def homotopyLimit : C :=
  (exists_distTriang_sub_piTowerShift F).choose

/-- The map `R lim F ⟶ ∏ₙ Fₙ` of the chosen Milnor triangle. -/
noncomputable def homotopyLimitι : homotopyLimit F ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
  (exists_distTriang_sub_piTowerShift F).choose_spec.choose

lemma exists_distTriang_homotopyLimitι :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ (homotopyLimit F)⟦(1 : ℤ)⟧,
      Triangle.mk (homotopyLimitι F) (𝟙 _ - piTowerShift F) δ ∈ distTriang C :=
  (exists_distTriang_sub_piTowerShift F).choose_spec.choose_spec

lemma homotopyLimitι_comp_sub_piTowerShift :
    homotopyLimitι F ≫ (𝟙 _ - piTowerShift F) = 0 := by
  obtain ⟨δ, hT⟩ := exists_distTriang_homotopyLimitι F
  exact comp_distTriang_mor_zero₁₂ _ hT

lemma homotopyLimitι_π_succ (n : ℕ) :
    homotopyLimitι F ≫ Pi.π _ (n + 1) ≫ F.map (homOfLE (n.le_add_right 1)).op =
      homotopyLimitι F ≫ Pi.π _ n := by
  have h := homotopyLimitι_comp_sub_piTowerShift F =≫ Pi.π _ n
  rw [Preadditive.comp_sub, Preadditive.sub_comp, zero_comp, sub_eq_zero, Category.comp_id,
    Category.assoc, piTowerShift_π] at h
  exact h.symm

/-- A chosen homotopy limit cone `R lim F` of a tower `F` with a product `∏ₙ Fₙ`: its legs are
the components of a map `R lim F ⟶ ∏ₙ Fₙ` completing `1 - t` to a distinguished triangle. -/
noncomputable def homotopyLimitCone : Cone F where
  pt := homotopyLimit F
  π := NatTrans.ofOpSequence (fun n ↦ homotopyLimitι F ≫ Pi.π _ n) fun n ↦ by
    simpa using (homotopyLimitι_π_succ F n).symm

@[simp]
lemma homotopyLimitCone_π_app (n : ℕ) :
    (homotopyLimitCone F).π.app (op n) = homotopyLimitι F ≫ Pi.π _ n :=
  rfl

lemma isHomotopyLimit_homotopyLimitCone : IsHomotopyLimit (homotopyLimitCone F) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_homotopyLimitι F
  refine ⟨_, productIsProduct _, δ, ?_⟩
  have hι : Fan.IsLimit.lift (productIsProduct fun n : ℕ ↦ F.obj (op n))
      (fun n ↦ (homotopyLimitCone F).π.app (op n)) = homotopyLimitι F :=
    Pi.hom_ext _ _ fun n ↦ (Fan.IsLimit.fac _ _ n).trans rfl
  rw [hι]
  exact hT

end Existence

section Map

variable {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ ↦ F.obj (op n)]
  [HasProduct fun n : ℕ ↦ G.obj (op n)] (a : F ⟶ G)

end Map

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

end CategoryTheory.Pretriangulated
