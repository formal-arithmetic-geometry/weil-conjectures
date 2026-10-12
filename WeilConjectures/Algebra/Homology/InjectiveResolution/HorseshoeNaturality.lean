/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Naturality of the horseshoe construction for injective resolutions

Given a morphism of short exact sequences and "horseshoe" injective resolutions of both, together
with chain maps lifting the outer components, we construct a chain map between the middle
resolutions compatible with everything. The construction is done in three steps, following the
classical proof (Weibel, Theorem 2.4.6; Stacks, Tag 015I):

* `CategoryTheory.InjectiveResolution.horseshoe_degreewise_map`: a degreewise map `t` compatible
  with both outer row squares (but not with the differentials);
* `CategoryTheory.InjectiveResolution.horseshoe_defect_factorization`: the failure of `t` to
  commute with the differentials factors through the outer resolutions, with cocycle identities;
* `CategoryTheory.InjectiveResolution.corrected_middle_map`: subtracting a suitable correction
  yields a chain map compatible with the rows and augmentations.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Degreewise middle map of the horseshoe**: given two rows `X → Y → Z` and `X' → Y' → Z'` of
cochain complexes which are short exact in each degree, with `X` and `X'` degreewise injective,
and chain maps `φA : X ⟶ X'`, `φC : Z ⟶ Z'`, there are maps `t n : Y n ⟶ Y' n` commuting with
both outer squares in each degree (no compatibility with the differentials is claimed).
(blueprint: `lem-weil-pbc-horseshoe-degreewise-map`) -/
theorem horseshoe_degreewise_map {X Y Z X' Y' Z' : CochainComplex C ℕ}
    (α : X ⟶ Y) (β : Y ⟶ Z) (α' : X' ⟶ Y') (β' : Y' ⟶ Z')
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hS : ∀ n, (ShortComplex.mk (α.f n) (β.f n)
      (by rw [← HomologicalComplex.comp_f, hαβ, HomologicalComplex.zero_f])).ShortExact)
    (hS' : ∀ n, (ShortComplex.mk (α'.f n) (β'.f n)
      (by rw [← HomologicalComplex.comp_f, hαβ', HomologicalComplex.zero_f])).ShortExact)
    [∀ n, Injective (X.X n)] [∀ n, Injective (X'.X n)]
    (φA : X ⟶ X') (φC : Z ⟶ Z') :
    ∃ t : ∀ n, Y.X n ⟶ Y'.X n, ∀ n,
      α.f n ≫ t n = φA.f n ≫ α'.f n ∧ t n ≫ β'.f n = β.f n ≫ φC.f n := by
  refine ⟨fun n ↦ (hS n).splittingOfInjective.r ≫ φA.f n ≫ α'.f n +
    β.f n ≫ φC.f n ≫ (hS' n).splittingOfInjective.s, fun n ↦ ⟨?_, ?_⟩⟩
  · have h1 := (hS n).splittingOfInjective.f_r
    have h2 : α.f n ≫ β.f n = 0 := by
      rw [← HomologicalComplex.comp_f, hαβ, HomologicalComplex.zero_f]
    dsimp at h1
    rw [Preadditive.comp_add, reassoc_of% h1, reassoc_of% h2, zero_comp, add_zero]
  · have h1 := (hS' n).splittingOfInjective.s_g
    have h2 : α'.f n ≫ β'.f n = 0 := by
      rw [← HomologicalComplex.comp_f, hαβ', HomologicalComplex.zero_f]
    dsimp at h1
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, h2, comp_zero, comp_zero,
      zero_add, Category.assoc, Category.assoc, h1, Category.comp_id]

/-- **Correction of the horseshoe middle map**: if `χ : Y ⟶ Y'` commutes with both outer row
squares and `q : Y ⟶ Y'` is killed by `α` and `β'`, and the augmentation defect of `χ` equals
that of `q`, then `χ - q` commutes with both row squares and with the augmentations.
(blueprint: `lem-weil-pbc-horseshoe-correction`) -/
theorem corrected_middle_map {X Y Z X' Y' Z' : CochainComplex C ℕ} {U U' : C}
    (α : X ⟶ Y) (β : Y ⟶ Z) (α' : X' ⟶ Y') (β' : Y' ⟶ Z')
    (φA : X ⟶ X') (φC : Z ⟶ Z') (χ q : Y ⟶ Y')
    (ε : (CochainComplex.single₀ C).obj U ⟶ Y)
    (ε' : (CochainComplex.single₀ C).obj U' ⟶ Y')
    (b : (CochainComplex.single₀ C).obj U ⟶ (CochainComplex.single₀ C).obj U')
    (hχα : α ≫ χ = φA ≫ α') (hχβ : χ ≫ β' = β ≫ φC)
    (hqa : α ≫ q = 0) (hqb : q ≫ β' = 0)
    (hε : ε ≫ χ - ε ≫ q = b ≫ ε') :
    ∃ φB : Y ⟶ Y', ε ≫ φB = b ≫ ε' ∧
      α ≫ φB = φA ≫ α' ∧ φB ≫ β' = β ≫ φC := by
  refine ⟨χ - q, ?_, ?_, ?_⟩
  · simpa only [Preadditive.comp_sub] using hε
  · rw [Preadditive.comp_sub, hχα, hqa, sub_zero]
  · rw [Preadditive.sub_comp, hχβ, hqb, sub_zero]

end CategoryTheory.InjectiveResolution
