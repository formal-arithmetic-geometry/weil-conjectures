/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The geometric Frobenius of an algebraic extension of a finite field

Mathlib's `FiniteField.frobeniusAlgEquivOfAlgebraic K L` is the *arithmetic* Frobenius
`σ : x ↦ x ^ #K` of an algebraic extension `L` of a finite field `K`, viewed as an element of
the group `Gal(L/K) = L ≃ₐ[K] L`. The *geometric* Frobenius is its inverse, and it is the
automorphism that acts on étale cohomology in the Weil conjectures.

## Main definitions

- `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`: the geometric Frobenius `σ⁻¹`.

## Main statements

- `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_mul_frobeniusAlgEquivOfAlgebraic`: the
  geometric and the arithmetic Frobenius are mutually inverse.
-/

@[expose] public section

namespace FiniteField

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- Blueprint `sk-d-ab-field`: Finite fields, Frobenius and abelian varieties.

Fix a finite field `K` with `q` elements and an algebraic extension `L`. The *arithmetic
Frobenius* is `σ : x ↦ x ^ q`; the *geometric Frobenius* is `F = σ⁻¹`. -/
noncomputable def geometricFrobeniusAlgEquivOfAlgebraic : Gal(L/K) :=
  (frobeniusAlgEquivOfAlgebraic K L)⁻¹

/-- The geometric Frobenius is inverse to the arithmetic Frobenius. -/
theorem geometricFrobeniusAlgEquivOfAlgebraic_mul_frobeniusAlgEquivOfAlgebraic :
    geometricFrobeniusAlgEquivOfAlgebraic K L * frobeniusAlgEquivOfAlgebraic K L = 1 :=
  inv_mul_cancel _

end FiniteField
