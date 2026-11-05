/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import WeilConjectures.ZetaLinearAlgebra.IntegralRecurrence
public import WeilConjectures.ZetaLinearAlgebra.NormalizedGauss

/-!
# The integral Fatou theorem

A power series with integer coefficients that is rational over `ℚ` is rational over `ℤ`: it can
be written as `A / B` with `A` and `B` integer polynomials whose constant coefficients are `1`.
This file combines the integral rational presentation
(`PowerSeries.exists_int_normalized_fraction'`) with the normalized Gauss lemma
(`Polynomial.exists_reduced_int_fraction`) to obtain the reduced form of such a presentation,
and to show that it is unique.

## Main statements

- `PowerSeries.exists_unique_reduced_int_fraction`: **the integral Fatou theorem**. An integral
  power series with constant coefficient `1` that is rational over `ℚ` has a *unique* pair of
  integer polynomials `(A, B)` with constant coefficients `1`, coprime over `ℚ`, and `f * B = A`.
- `PowerSeries.exists_int_fraction_of_rational`: the plain existence statement in the form the
  zeta function application needs, with the identity read in `ℚ⟦X⟧`.
-/

@[expose] public section

open Polynomial

namespace PowerSeries

/-- A power series with integer coefficients that is rational over `ℚ` is the quotient of two
integer polynomials with constant coefficient `1`, the identity being read in `ℚ⟦X⟧`. This is
the form in which rationality of a zeta function is stated. -/
theorem exists_int_fraction_of_rational (f : ℤ⟦X⟧)
    (h : ∃ A B : ℚ[X], B.coeff 0 = 1 ∧
      map (Int.castRingHom ℚ) f * (B : ℚ⟦X⟧) = (A : ℚ⟦X⟧)) :
    ∃ P Q : ℤ[X], Q.coeff 0 = 1 ∧
      map (Int.castRingHom ℚ) f * (Q.map (Int.castRingHom ℚ) : ℚ⟦X⟧) =
        (P.map (Int.castRingHom ℚ) : ℚ⟦X⟧) := by
  obtain ⟨P, Q, hQ, hPQ⟩ := exists_int_normalized_fraction f h
  refine ⟨P, Q, hQ, ?_⟩
  rw [Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe, ← map_mul, hPQ]

end PowerSeries
