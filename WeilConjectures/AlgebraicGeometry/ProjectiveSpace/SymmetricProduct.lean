/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# The symmetric product morphism `(ℙ¹)ⁿ ⟶ ℙⁿ`

For a scheme `S` and `n : ℕ`, write `(ℙ¹_S)ⁿ` for the `n`-fold fibre power of the projective
line over `S`, realised as the tower `ℙ¹_{ℙ¹_{⋯ S}}`
(`AlgebraicGeometry.ProjectiveSpace.projectiveLinePow`). The polynomials `F₀, …, Fₙ` defined by

`∏ᵢ (xᵢ t + yᵢ) = ∑ⱼ Fⱼ tʲ`

are multihomogeneous of degree one in every pair `(xᵢ, yᵢ)`, have no common zero and are
invariant under permutation of the factors; they define the *symmetric product morphism*
`σₙ : (ℙ¹_S)ⁿ ⟶ ℙⁿ_S`, which is finite and surjective. Over an algebraically closed field this
says that a binary form of degree `n` factors as a product of `n` linear forms.

This is the step from `ℙ¹` to `ℙⁿ` in the reduction of proper base change to the projective
line.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.projectiveLinePow`: the tower `(ℙ¹_S)ⁿ`.
- `AlgebraicGeometry.ProjectiveSpace.projectiveLinePowProj`: its projection to `S`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.exists_isFinite_surjective_projectiveLinePow`: for every
  finite nonempty index type `n` there are `k` and a finite surjective morphism
  `(ℙ¹_S)ᵏ ⟶ ℙ(n; S)` over `S`.

## References

- Stacks Project, proof of Lemma 59.91.10, <https://stacks.math.columbia.edu/tag/0A4F>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- The `n`-fold fibre power `(ℙ¹_S)ⁿ` of the projective line over `S`, realised as the tower
`(ℙ¹_S)⁰ = S` and `(ℙ¹_S)ⁿ⁺¹ = ℙ¹_{(ℙ¹_S)ⁿ}`. -/
noncomputable def projectiveLinePow : ℕ → Scheme.{u} → Scheme.{u}
  | 0, S => S
  | n + 1, S => ProjectiveLine (projectiveLinePow n S)

/-- The projection `(ℙ¹_S)ⁿ ⟶ S`, the composite of the projections of the projective lines of
the tower `AlgebraicGeometry.ProjectiveSpace.projectiveLinePow`. -/
noncomputable def projectiveLinePowProj : (n : ℕ) → (S : Scheme.{u}) → projectiveLinePow n S ⟶ S
  | 0, S => 𝟙 S
  | n + 1, S => (ProjectiveLine (projectiveLinePow n S) ↘ projectiveLinePow n S) ≫
      projectiveLinePowProj n S

/-- **The symmetric product morphism is finite and surjective.** For a finite nonempty index
type `n` with `k + 1` elements there is a finite surjective morphism `σ : (ℙ¹_S)ᵏ ⟶ ℙ(n; S)` over
`S`: the symmetric product morphism `((xᵢ : yᵢ))ᵢ ↦ [F₀ : ⋯ : Fₖ]` with
`∏ᵢ (xᵢ t + yᵢ) = ∑ⱼ Fⱼ tʲ`. It is finite because each `zᵢ = xᵢ / yᵢ` is a root of the monic
polynomial `Tᵏ - e₁ Tᵏ⁻¹ + ⋯ ± eₖ` over the elementary symmetric functions (and likewise on the
other charts), and surjective because a binary form of degree `k` over an algebraically closed
field is a product of `k` linear forms.
(blueprint: `lemma-weil-pbc-symmetric-product-p1`, `lem-weil-pbc-symmetric-product-finite`,
`lem-weil-pbc-symmetric-product-surjective`) -/
theorem exists_isFinite_surjective_projectiveLinePow (n : Type u) [Finite n] [Nonempty n]
    (S : Scheme.{u}) :
    ∃ (k : ℕ) (σ : projectiveLinePow k S ⟶ ℙ(n; S)), IsFinite σ ∧ Surjective σ ∧
      σ ≫ ℙ(n; S) ↘ S = projectiveLinePowProj k S :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
