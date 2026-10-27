/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.PolynomialRankOneDifferenceModelData

/-! Existence of the finite polynomial system used by the rank-one model. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
open Profinite.CondensedAction.IndUnipotent
open Profinite.CondensedAction.ContinuousRepresentation
open Profinite.CondensedAction.PrimeToEll
open scoped TensorProduct
namespace Profinite.CondensedAction.PolynomialRankOne

/-- The degree filtration of the polynomial algebra is a finite ind-unipotent system.
Source: latest blueprint, direct-images proof (3), expanded proof of
lem-sfb-polynomial-rank-one-difference-model, steps 1--5
(blueprint: lem-sfb-polynomial-rank-one-system-existence).

Proof: let I_n be the exponent vectors of total degree at most n, and take V_n to be
its coefficient-vector space, lifted to the required module universe. Each coordinate
of an exponent is at most n, so I_n is finite. Send its coordinate basis to the
corresponding monomials. Uniqueness of polynomial coefficients proves injectivity and
the image description. Extend coefficient vectors by zero for the transition maps.
These are injective and have exactly the required polynomial inclusion formula.

Substitute X_i minus the corresponding p-adic coordinate in every y variable and
leave the z variables fixed. Binomial expansion shows that this preserves total
degree and that each matrix entry is polynomial in the coordinates. Composition of
substitutions adds parameters; substitution by zero is identity. These formulas give
the representation law, equivariance of transitions, and the polynomialEntries field.
Coordinates in E are continuous. Finite sums and products prove continuity of the
matrix entries and joint continuity on the finite coefficient-vector spaces. Their
finite product topology is the module topology; E is a finite extension of Q_ell.

Restrict minus the first partial derivative to V_n. On a monomial with first exponent
a, its j-th iterate multiplies by (-1)^j times a(a-1)...(a-j+1) and lowers that exponent
by j. Thus its (n+1)-st power is zero. The same formula proves compatibility with the
inclusions; differentiation commutes with translations in the residual coordinates.
Set the exponent to n+1. Characteristic zero makes every j! invertible. Dividing the
falling-factorial formula by j! gives the binomial coefficient, and summing over
j from zero to n gives precisely translation of y_1 by minus t. This verifies the
exponential field and all the remaining PolynomialSystem and System fields.
For n=0 the space consists of constants and the derivative is zero; for k=0 or m=0
empty coordinate families give the same formulas. No existence theorem is used to
define the stage spaces or any of their maps. -/
theorem exists_polynomial_system
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (k m : ℕ) :
    Nonempty (PolynomialSystem ℓ E k m) := by
  sorry

end Profinite.CondensedAction.PolynomialRankOne
