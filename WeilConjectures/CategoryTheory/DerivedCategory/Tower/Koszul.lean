/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Completion
public import Mathlib.Algebra.Homology.Double

/-!
# Koszul complexes and the intrinsic Koszul completion

Let `A` be a monoidal abelian category which is linear over a commutative ring `R`, and let
`f₁, …, f_r ∈ R`. This file constructs, in the category of cochain complexes of `A`,

* the two-term complexes `[𝟙 --a--> 𝟙]` in degrees `-1` and `0`
  (`CochainComplex.twoTermComplex`), with the maps `[𝟙 --cb--> 𝟙] ⟶ [𝟙 --b--> 𝟙]` which are the
  multiplication by `c` in degree `-1` and the identity in degree `0`
  (`CochainComplex.twoTermComplexMap`);
* the Koszul complexes `K(𝟙; f₁, …, f_r) = ⊗ⱼ [𝟙 --fⱼ--> 𝟙]` (`CochainComplex.koszulComplex`)
  and their transition maps (`CochainComplex.koszulComplexMap`);
* the Koszul tower `m ↦ K(𝟙; f₁ᵐ, …, f_rᵐ)` (`CochainComplex.koszulTower`) together with its
  augmentation from the unit, given by the identity in degree `0`
  (`CochainComplex.koszulTowerAugmentation`).

When `A` is moreover a monoidal closed braided Grothendieck abelian category with functorial flat
resolutions, the derived limit of the reduction tower `m ↦ K ⊗ᴸ K(𝟙; fᵐ)` is the *intrinsic
Koszul completion* `K^{∧, Kos}` of `K ∈ D(A)` (`DerivedCategory.koszulCompletion`), with the map
`κ_K : K ⟶ K^{∧, Kos}` induced by the augmentations (`DerivedCategory.koszulCompletionMap`);
`K` is *derived complete* when `κ_K` is an isomorphism (`DerivedCategory.IsKoszulComplete`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory Opposite HomologicalComplex

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {R : Type w} [CommRing R] [Linear R A]

section TwoTerm

/-- The relation `-1 → 0` of the complex shape of cochain complexes. -/
lemma up_rel_neg_one_zero : (ComplexShape.up ℤ).Rel (-1) 0 := by simp

variable (A) in
/-- The two-term complex `[𝟙 --a--> 𝟙]` in degrees `-1` and `0`. -/
noncomputable abbrev twoTermComplex (a : R) : CochainComplex A ℤ :=
  double (a • 𝟙 (𝟙_ A)) up_rel_neg_one_zero

lemma twoTermComplex_d (a : R) :
    (twoTermComplex A a).d (-1) 0 =
      (doubleXIso₀ _ up_rel_neg_one_zero).hom ≫ (a • 𝟙 (𝟙_ A)) ≫
        (doubleXIso₁ _ up_rel_neg_one_zero (by omega)).inv :=
  double_d _ _ _

variable (A) in
/-- The map `[𝟙 --a--> 𝟙] ⟶ [𝟙 --b--> 𝟙]` for `a = c * b`, which is the multiplication by `c`
in degree `-1` and the identity in degree `0`. -/
noncomputable def twoTermComplexMap (a b c : R) (h : a = c * b) :
    twoTermComplex A a ⟶ twoTermComplex A b :=
  mkHomFromDouble _ (by omega) ((c • 𝟙 (𝟙_ A)) ≫ (doubleXIso₀ _ up_rel_neg_one_zero).inv)
    (doubleXIso₁ _ up_rel_neg_one_zero (by omega)).inv
    (by
      rw [twoTermComplex_d]
      simp [h, mul_smul])
    (by
      intro k hk
      rw [double_d_eq_zero₀ _ _ _ _ (by omega), comp_zero])

@[simp]
lemma twoTermComplexMap_f_neg_one (a b c : R) (h : a = c * b) :
    (twoTermComplexMap A a b c h).f (-1) =
      (doubleXIso₀ (a • 𝟙 (𝟙_ A)) up_rel_neg_one_zero).hom ≫ (c • 𝟙 (𝟙_ A)) ≫
        (doubleXIso₀ (b • 𝟙 (𝟙_ A)) up_rel_neg_one_zero).inv :=
  mkHomFromDouble_f₀ _ _ _ _ _ _

@[simp]
lemma twoTermComplexMap_f_zero (a b c : R) (h : a = c * b) :
    (twoTermComplexMap A a b c h).f 0 =
      (doubleXIso₁ (a • 𝟙 (𝟙_ A)) up_rel_neg_one_zero (by omega)).hom ≫
        (doubleXIso₁ (b • 𝟙 (𝟙_ A)) up_rel_neg_one_zero (by omega)).inv :=
  mkHomFromDouble_f₁ _ _ _ _ _ _

lemma twoTermComplexMap_one (a : R) :
    twoTermComplexMap A a a 1 (one_mul a).symm = 𝟙 _ := by
  ext <;> simp

@[reassoc]
lemma twoTermComplexMap_comp (a b d c e : R) (h : a = c * b) (h' : b = e * d) :
    twoTermComplexMap A a b c h ≫ twoTermComplexMap A b d e h' =
      twoTermComplexMap A a d (c * e) (by rw [h, h', mul_assoc]) := by
  ext <;> simp [mul_smul]

end TwoTerm

end CochainComplex
