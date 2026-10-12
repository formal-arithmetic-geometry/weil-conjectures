/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.FiniteMorphism
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product

/-!
# The symmetric-product cover of projective space

For `n ≥ 1` the polynomials `F₀, …, Fₙ` defined by `∏ᵢ (xᵢ t + yᵢ) = ∑ⱼ Fⱼ tʲ` define a morphism
`σₙ : (ℙ¹_S)ⁿ ⟶ ℙⁿ_S` (`def-weil-pbc-symmetric-product-morphism`), which is finite and
surjective (`lem-fin-symmetric-product-finite`). The fibre power `(ℙ¹_S)ⁿ` is the product
`∏ᶜ fun _ : Fin n ↦ ℙ¹_S` in `Over S`, as in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product`,
and `ℙⁿ_S` is `ℙ(ULift (Fin (n + 1)); S)`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.exists_isFinite_surjective_pi_projectiveLine`: there is a
  finite surjective morphism `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` over `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- Blueprint `lem-fin-symmetric-product-finite`: A finite symmetric-product cover over a
Noetherian base.

For a scheme `S` and `n : ℕ`, there is a finite surjective morphism `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` over `S`.
The blueprint states this for the symmetric-product morphism `σₙ` of
`def-weil-pbc-symmetric-product-morphism`, `n ≥ 1` and `S` Noetherian; here the morphism is the
witness of the existential, which is what the applications (`lem-finrepair-projective-from-line`)
use. -/
theorem exists_isFinite_surjective_pi_projectiveLine (S : Scheme.{u}) (n : ℕ) :
    ∃ σ : (∏ᶜ fun _ : Fin n ↦ Over.mk (ProjectiveLine S ↘ S)) ⟶
        Over.mk (ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S),
      IsFinite σ.left ∧ Surjective σ.left := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
