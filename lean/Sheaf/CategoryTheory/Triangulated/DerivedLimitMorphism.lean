/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit

/-!
# Morphisms between specified derived limits

Source: Stacks Project, Derived Categories, Remark Tag 0H9J, with `m(n) = n`
(blueprint: lem-weil-derived-limit-morphism).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

/-- A morphism of towers extends to a morphism between their specified Roos triangles.
Source: Stacks Project, Derived Categories, Remark Tag 0H9J, with `m(n) = n`
(blueprint: lem-weil-derived-limit-morphism).

Proof:
1. Write `a` for the product of the components of `φ`. The projection formula for
`Limits.Pi.map` and the naturality of `φ` show that `a` commutes with the product shifts.
Subtracting from the identity gives commutation with `towerTransitionEndomorphism`
(`def-weil-category-product`, `def-weil-inverse-system`,
`def-weil-tower-transition-endomorphism`, `def-weil-triangulated-category`).
2. Rotate both given distinguished Roos triangles by TR2. Their first square, with
vertical arrows `a, a`, commutes by step 1. TR3 completes it with a map
`c : L⟦1⟧ ⟶ L'⟦1⟧` compatible with the connecting maps and the negatives of the
shifted projection maps (`def-weil-triangulated-category`).
3. Fullness of the shift gives `ψ` with `ψ⟦1⟧' = c`. Cancel the two minus signs
in the last square and use faithfulness of the shift to obtain `ψ ≫ p' = p ≫ a`.
The other square is `δ ≫ ψ⟦1⟧' = a ≫ δ'`. These and step 1 give the morphism
of triangles. TR3 gives existence only; no uniqueness or functorial choice is asserted.
The index `n : ℕ` represents the paper's level `n + 1`. -/
theorem exists_derivedLimit_morphism {C : Type u} [Category.{v} C]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {K K' : ℕ → C} [HasProduct K] [HasProduct K']
    (f : ∀ n : ℕ, K (n + 1) ⟶ K n) (f' : ∀ n : ℕ, K' (n + 1) ⟶ K' n)
    (L L' : C) (p : L ⟶ ∏ᶜ K) (p' : L' ⟶ ∏ᶜ K')
    (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧) (δ' : ∏ᶜ K' ⟶ L'⟦(1 : ℤ)⟧)
    (hL : IsDerivedLimitTriangle f L p δ) (hL' : IsDerivedLimitTriangle f' L' p' δ')
    (φ : Functor.ofOpSequence f ⟶ Functor.ofOpSequence f') :
    ∃ ψ : L ⟶ L',
      ψ ≫ p' = p ≫ Limits.Pi.map (f := K) (g := K') (fun n : ℕ ↦ φ.app ⟨n⟩) ∧
      δ ≫ ψ⟦(1 : ℤ)⟧' =
        Limits.Pi.map (f := K) (g := K') (fun n : ℕ ↦ φ.app ⟨n⟩) ≫ δ' := by
  sorry

end CategoryTheory
