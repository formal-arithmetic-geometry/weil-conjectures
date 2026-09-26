/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

/-!
# The radius of convergence of a formal power series

A formal power series `f = ∑ aₙ Tⁿ ∈ ℂ⟦X⟧` has a radius of convergence `R(f) ∈ ℝ≥0∞`, the
supremum of all `r ≥ 0` such that `∑ₙ |aₙ| tⁿ` converges for every `0 ≤ t < r`.

Rather than redoing the classical theory we reduce to Mathlib's radius of convergence of a
formal multilinear series: the scalar series `∑ aₙ Tⁿ` is `FormalMultilinearSeries.ofScalars`
applied to the coefficients of `f`, and `FormalMultilinearSeries.radius` of that series is the
usual radius of convergence.

This file also introduces nonnegative series, those all of whose coefficients lie in `ℝ≥0`.

## Main definitions

- `PowerSeries.radius` : the radius of convergence `R(f) ∈ ℝ≥0∞` of `f : ℂ⟦X⟧`.
- `PowerSeries.IsNonneg` : all coefficients of `f : ℂ⟦X⟧` are nonnegative reals.
-/

open scoped ENNReal NNReal

namespace PowerSeries

/-- Blueprint `sk-d-real-series`: Radius of a formal series.

The radius of convergence `R(f) ∈ ℝ≥0∞` of a formal power series `f = ∑ aₙ Tⁿ ∈ ℂ⟦X⟧`.

This is defined as the radius of convergence of the associated formal multilinear series
`FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n f)`, whose `n`-th coefficient is `aₙ` by
`FormalMultilinearSeries.coeff_ofScalars`. It agrees with the description in the blueprint as
the supremum of the `r ≥ 0` for which `∑ₙ |aₙ| tⁿ` converges for all `0 ≤ t < r`: by
`FormalMultilinearSeries.radius` it is the supremum of the `r ≥ 0` for which `‖aₙ‖ rⁿ` is
bounded, and boundedness of `‖aₙ‖ rⁿ` for one `r` is equivalent to summability of
`∑ₙ ‖aₙ‖ tⁿ` for all `t < r` (`FormalMultilinearSeries.summable_norm_mul_pow` and
`FormalMultilinearSeries.le_radius_of_summable_norm`). -/
noncomputable def radius (f : ℂ⟦X⟧) : ℝ≥0∞ :=
  (FormalMultilinearSeries.ofScalars ℂ fun n ↦ coeff n f).radius

/-- Blueprint `sk-d-real-series`: Radius of a formal series.

A formal power series `f = ∑ aₙ Tⁿ ∈ ℂ⟦X⟧` is nonnegative if all of its coefficients `aₙ` are
nonnegative real numbers. Such series are the ones for which the coefficientwise comparison
arguments of the real-sheaves chapter apply. -/
def IsNonneg (f : ℂ⟦X⟧) : Prop :=
  ∀ n, ∃ a : ℝ≥0, coeff n f = ((a : ℝ) : ℂ)

end PowerSeries
