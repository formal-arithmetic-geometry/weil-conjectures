/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# The symmetric-product morphism `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S`

For a scheme `S` and `n : ℕ`, the `n`-fold fibre power `(ℙ¹_S)ⁿ` of the projective line is
`AlgebraicGeometry.ProjectiveLine.pow S n`, built as the iterated projective line
`ℙ¹_{(ℙ¹_S)ⁿ⁻¹}`, so that its structure morphism to `S` is by definition a composite of `n`
projective-line projections. The symmetric-product morphism
`AlgebraicGeometry.ProjectiveSpace.symmetricProduct S n : (ℙ¹_S)ⁿ ⟶ ℙⁿ_S` sends a tuple of
points `[x_i : y_i]` to the coefficients `[F_0 : ⋯ : F_n]` of the binary form
`∏ᵢ (x_i t + y_i) = ∑ⱼ F_j tʲ`.

## Main definitions

- `AlgebraicGeometry.ProjectiveLine.pow`: the fibre power `(ℙ¹_S)ⁿ`.
- `AlgebraicGeometry.ProjectiveSpace.symmetricProduct`: the morphism `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.isFinite_symmetricProduct`: it is finite.
- `AlgebraicGeometry.ProjectiveSpace.surjective_symmetricProduct`: it is surjective.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

noncomputable section

open Scheme

/-- The `n`-fold fibre power `(ℙ¹_S)ⁿ` of the projective line over `S`, built as an iterated
projective line: `(ℙ¹_S)⁰ = S` and `(ℙ¹_S)ⁿ⁺¹ = ℙ¹_{(ℙ¹_S)ⁿ}`. -/
def ProjectiveLine.pow (S : Scheme.{u}) : ℕ → Scheme.{u}
  | 0 => S
  | n + 1 => ProjectiveLine (ProjectiveLine.pow S n)

/-- The structure morphism `(ℙ¹_S)ⁿ ⟶ S`, the composite of the `n` projective-line
projections. -/
def ProjectiveLine.powOver (S : Scheme.{u}) : (n : ℕ) → ProjectiveLine.pow S n ⟶ S
  | 0 => 𝟙 S
  | n + 1 => ProjectiveLine (ProjectiveLine.pow S n) ↘ ProjectiveLine.pow S n ≫
      ProjectiveLine.powOver S n

namespace ProjectiveLine

variable (S : Scheme.{u})

@[simp]
lemma powOver_zero : powOver S 0 = 𝟙 S := rfl

lemma powOver_succ (n : ℕ) :
    powOver S (n + 1) = ProjectiveLine (pow S n) ↘ pow S n ≫ powOver S n := rfl

instance isProper_powOver (n : ℕ) : IsProper (powOver S n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProper (𝟙 S))
  | succ n ih => rw [powOver_succ]; infer_instance

end ProjectiveLine

namespace ProjectiveSpace

/-- **The symmetric-product morphism** `σₙ : (ℙ¹_S)ⁿ ⟶ ℙⁿ_S`, sending `([x_i : y_i])_i` to
`[F_0 : ⋯ : F_n]`, where `∏ᵢ (x_i t + y_i) = ∑ⱼ F_j tʲ`.
(blueprint: `def-weil-pbc-symmetric-product-morphism`) -/
def symmetricProduct (S : Scheme.{u}) (n : ℕ) :
    ProjectiveLine.pow S n ⟶ ℙ(ULift.{u} (Fin (n + 1)); S) :=
  sorry

/-- The symmetric-product morphism is a morphism over `S`. -/
@[reassoc (attr := simp)]
lemma symmetricProduct_over (S : Scheme.{u}) (n : ℕ) :
    symmetricProduct S n ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = ProjectiveLine.powOver S n :=
  sorry

/-- **The symmetric-product morphism is finite.**
(blueprint: `lem-weil-pbc-symmetric-product-finite`) -/
theorem isFinite_symmetricProduct (S : Scheme.{u}) (n : ℕ) :
    IsFinite (symmetricProduct S n) :=
  sorry

/-- **The symmetric-product morphism is surjective.**
(blueprint: `lem-weil-pbc-symmetric-product-surjective`) -/
theorem surjective_symmetricProduct (S : Scheme.{u}) (n : ℕ) :
    Surjective (symmetricProduct S n) :=
  sorry

end ProjectiveSpace

end

end AlgebraicGeometry
