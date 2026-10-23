/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Basic
public import WeilConjectures.TraceFormula.CategoricalTrace

/-!

# Additivity of categorical traces along long exact sequences

Let `C` be an abelian braided monoidal category whose tensor product is additive, and such that
`K = End (𝟙_ C)` is a field: every nonzero endomorphism of the unit is invertible. An object is
*finite free* (`CategoryTheory.MonoidalCategory.IsFiniteFree`) if it is a finite biproduct of
copies of the unit `𝟙_ C`. Finite free objects are dualizable, morphisms between them are matrices
over `K`, and the categorical trace of an endomorphism is the trace of its matrix.

For a bounded long exact sequence
`⋯ ⟶ Aʲ ⟶ Bʲ ⟶ Dʲ ⟶ Aʲ⁺¹ ⟶ ⋯` of finite free objects with endomorphisms commuting with all
the maps, the alternating sums of the traces satisfy `STr(B) = STr(A) + STr(D)`
(`CategoryTheory.superTrace_eq_add_of_exact`).

## Main definitions

- `CategoryTheory.MonoidalCategory.IsFiniteFree`: finite biproducts of copies of the unit.

## Main results

- `CategoryTheory.superTrace_eq_add_of_exact`: additivity of supertraces along bounded long
  exact sequences of finite free objects.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- An object is *finite free* if it is isomorphic to a finite biproduct of copies of the
monoidal unit. -/
def MonoidalCategory.IsFiniteFree (X : C) : Prop :=
  ∃ n : ℕ, Nonempty (X ≅ ⨁ fun _ : Fin n ↦ 𝟙_ C)

/-- **Additivity of supertraces along long exact sequences.** Let `End (𝟙_ C)` be a field, and
let `⋯ ⟶ Aʲ ⟶ Bʲ ⟶ Dʲ ⟶ Aʲ⁺¹ ⟶ ⋯` be a long exact sequence of finite free objects, zero outside a
finite range of degrees, with endomorphisms `φ_A`, `φ_B`, `φ_D` commuting with all the maps.
Then `∑ⱼ (-1)ʲ Tr(φ_Bʲ) = ∑ⱼ (-1)ʲ Tr(φ_Aʲ) + ∑ⱼ (-1)ʲ Tr(φ_Dʲ)`. -/
theorem superTrace_eq_add_of_exact (hK : ∀ t : End (𝟙_ C), t ≠ 0 → IsIso t)
    (h₁ : (1 : End (𝟙_ C)) ≠ 0) {A B D : ℤ → C} (φA : ∀ j, A j ⟶ A j) (φB : ∀ j, B j ⟶ B j)
    (φD : ∀ j, D j ⟶ D j) (u : ∀ j, A j ⟶ B j) (v : ∀ j, B j ⟶ D j) (w : ∀ j, D j ⟶ A (j + 1))
    (hu : ∀ j, φA j ≫ u j = u j ≫ φB j) (hv : ∀ j, φB j ≫ v j = v j ≫ φD j)
    (hw : ∀ j, φD j ≫ w j = w j ≫ φA (j + 1))
    (huv : ∀ j, u j ≫ v j = 0) (hvw : ∀ j, v j ≫ w j = 0) (hwu : ∀ j, w j ≫ u (j + 1) = 0)
    (ex₁ : ∀ j, (ShortComplex.mk _ _ (huv j)).Exact)
    (ex₂ : ∀ j, (ShortComplex.mk _ _ (hvw j)).Exact)
    (ex₃ : ∀ j, (ShortComplex.mk _ _ (hwu j)).Exact)
    (hA : ∀ j, IsFiniteFree (A j)) (hB : ∀ j, IsFiniteFree (B j)) (hD : ∀ j, IsFiniteFree (D j))
    (hbdd : ∃ a b : ℤ, ∀ j, (j < a ∨ b < j) → IsZero (A j) ∧ IsZero (B j) ∧ IsZero (D j)) :
    superTrace B φB = superTrace A φA + superTrace D φD :=
  sorry

end CategoryTheory
