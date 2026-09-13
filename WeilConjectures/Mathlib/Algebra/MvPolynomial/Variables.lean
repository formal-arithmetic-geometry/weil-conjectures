/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Variables of a prime polynomial over a field

## Main results

* `MvPolynomial.vars_nonempty_of_prime`: a prime element of a polynomial ring over a field
  involves at least one variable.
-/

@[expose] public section

namespace MvPolynomial

variable {σ k : Type*} [Field k]

/-- A prime element of a polynomial ring over a field involves at least one variable: a constant
polynomial is either zero or a unit. -/
theorem vars_nonempty_of_prime {g : MvPolynomial σ k} (hg : Prime g) : g.vars.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, Ne, vars_eq_empty_iff_eq_C]
  intro hv
  have hc0 : g.coeff 0 ≠ 0 := fun h ↦ hg.ne_zero (by rw [hv, h, map_zero])
  exact hg.not_isUnit (hv ▸ (isUnit_iff_ne_zero.mpr hc0).map C)

end MvPolynomial
