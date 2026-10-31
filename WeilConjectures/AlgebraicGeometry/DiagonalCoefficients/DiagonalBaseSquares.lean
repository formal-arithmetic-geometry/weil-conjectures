/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback

/-! # The actual three squares for diagonal base change

Source: coefficient changes, paragraph (3a).
(blueprint: lem-diagonal-base-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The projective-line product maps commute with its diagonal and both
projections over every scheme morphism. No flatness assumption is needed.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3a).
(blueprint: lem-diagonal-base-squares).

Proof: the first and second projection squares are the defining projection
identities of pullback.map. For the diagonal square, compose both maps with
each product projection and use the diagonal projection identities. Pullback
hom extensionality then proves the equality. -/
theorem diagonalBaseSquares {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) : BaseSquares g where
  diagonal_square := by
    apply pullback.hom_ext <;>
      simp [diagonalImmersion, baseW, Category.assoc]
  first_square := by
    simp [baseW]
  second_square := by
    simp [baseW]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
