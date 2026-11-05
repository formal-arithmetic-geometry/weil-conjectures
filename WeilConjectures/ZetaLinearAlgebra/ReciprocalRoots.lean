/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Polynomial.FieldDivision
public import WeilConjectures.Mathlib.Algebra.Polynomial.Splits
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import WeilConjectures.ZetaLinearAlgebra.Fatou

/-!
# Ordinary roots, reciprocal roots and normalized integral fractions

Let `P` be a polynomial over a field with `P(0) = 1`. Its *ordinary roots* are its roots `β`;
they are nonzero. Its *reciprocal roots* are the nonzero `α` with `P(α⁻¹) = 0`; they are the
roots of the reversed polynomial `P.reverse`, and if `P` splits then
`P = ∏ (1 - α X)` over its reciprocal roots `α`, counted with multiplicity
(blueprint `def-weil-ordinary-reciprocal-roots`).

For an endomorphism `f` of a finite-dimensional vector space over an algebraically closed field,
the reciprocal roots of `det (1 - X f)` are the nonzero eigenvalues of `f`, with algebraic
multiplicity (blueprint `prop-weil-reciprocal-roots-eigenvalues`).

Finally, we name the normalized reduced integral presentations `Z = A / B` of an integral power
series (blueprint `def-weil-normalized-integral-fraction`) and restate the integral Fatou
theorem in these terms (blueprint `prop-weil-integral-rational-series`).

## Main declarations

- `Polynomial.reverse_multiset_prod_one_sub_C_mul_X`: the reverse of `∏ (1 - a X)` is
  `∏ (X - a)` when no `a` vanishes.
- `Polynomial.ordinary_reciprocal_roots`: blueprint `def-weil-ordinary-reciprocal-roots`.
- `LinearMap.roots_reverse_charpolyRev`, `LinearMap.reciprocal_roots_eigenvalues`: blueprint
  `prop-weil-reciprocal-roots-eigenvalues`.
- `PowerSeries.IsNormalizedIntegralFraction`: blueprint `def-weil-normalized-integral-fraction`.
- `PowerSeries.existsUnique_isNormalizedIntegralFraction`: blueprint
  `prop-weil-integral-rational-series`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

section CommRing

variable {R : Type*} [CommRing R] [IsDomain R]

end CommRing

variable {K : Type*} [Field K]

end Polynomial

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [IsAlgClosed K] [DecidableEq K]

end LinearMap

namespace PowerSeries

end PowerSeries
