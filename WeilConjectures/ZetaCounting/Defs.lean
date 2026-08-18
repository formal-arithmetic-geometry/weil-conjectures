/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Log

@[expose] public section

/-!
# The zeta series of a counting function

A counting function is a function `c : ℕ → ℕ`, thought of as `n ↦ #X(𝔽_{qⁿ})` for a
variety `X` over a finite field, or as `n ↦ #{x | Fⁿ x = x}` for a self-map `F`. Its zeta
series is the formal power series

`Z_c(X) = Exp (∑_{n ≥ 1} c n * Xⁿ / n) ∈ ℚ⟦X⟧`.

This file introduces `PowerSeries.countingLogSeries` and `PowerSeries.countingZetaSeries`
and records the two facts that characterise the latter: it has constant coefficient `1`
and it solves the logarithmic differential equation `X * Z' = (∑_{n ≥ 1} c n Xⁿ) * Z`.

The zeta series of a scheme over a finite field,
`AlgebraicGeometry.Scheme.Hom.zetaSeries`, is by definition the zeta series of its point
counting function; see `WeilConjectures.ZetaCounting.Comparison`.

## Main definitions

- `PowerSeries.countingLogSeries`
- `PowerSeries.countingZetaSeries`

## Main results

- `PowerSeries.constantCoeff_countingZetaSeries`
- `PowerSeries.X_mul_derivative_countingZetaSeries`
- `PowerSeries.countingZetaSeries_congr`, the zeta series only sees the positive-index
  values of the counting function
-/

namespace PowerSeries

noncomputable section

variable (c : ℕ → ℕ)

/-- The logarithm series `∑_{n ≥ 1} c n * Xⁿ / n ∈ ℚ⟦X⟧` of a counting function `c`.
(blueprint: `def:weil-counting-log-series`) -/
def countingLogSeries : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then 0 else (c n : ℚ) / n

/-- The zeta series `Exp (∑_{n ≥ 1} c n * Xⁿ / n) ∈ ℚ⟦X⟧` of a counting function `c`.
(blueprint: `def:weil-counting-zeta-series`) -/
def countingZetaSeries : ℚ⟦X⟧ :=
  expOf (countingLogSeries c)

@[simp]
theorem coeff_countingLogSeries (n : ℕ) :
    coeff n (countingLogSeries c) = if n = 0 then 0 else (c n : ℚ) / n :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_countingLogSeries : constantCoeff (countingLogSeries c) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_countingLogSeries, if_pos rfl]

/-- The zeta series of a counting function is normalized.
(blueprint: `lemma:weil-counting-zeta-series-constant`) -/
@[simp]
theorem constantCoeff_countingZetaSeries : constantCoeff (countingZetaSeries c) = 1 :=
  constantCoeff_expOf (constantCoeff_countingLogSeries c)

/-- The logarithmic derivative of the logarithm series of `c` is the generating series
of `c`. (blueprint: `lemma:weil-counting-log-series-derivative`) -/
theorem X_mul_derivative_countingLogSeries :
    X * d⁄dX ℚ (countingLogSeries c) = mk fun n ↦ if n = 0 then (0 : ℚ) else c n := by
  ext n
  match n with
  | 0 => simp
  | m + 1 =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_countingLogSeries, coeff_mk,
      if_neg m.succ_ne_zero, if_neg m.succ_ne_zero]
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    rw [div_mul_cancel₀ _ hm]

/-- The logarithmic differential equation satisfied by the zeta series of a counting
function: `X * Z' = (∑_{n ≥ 1} c n Xⁿ) * Z`. Together with
`PowerSeries.constantCoeff_countingZetaSeries` this characterises the zeta series.
(blueprint: `lemma:weil-counting-zeta-series-derivative`) -/
theorem X_mul_derivative_countingZetaSeries :
    X * d⁄dX ℚ (countingZetaSeries c) =
      (mk fun n ↦ if n = 0 then (0 : ℚ) else c n) * countingZetaSeries c := by
  rw [countingZetaSeries, derivative_expOf (constantCoeff_countingLogSeries c), ← mul_assoc,
    X_mul_derivative_countingLogSeries]

/-- The zeta series only depends on the positive-index values of the counting function.
(blueprint: `lemma:weil-counting-zeta-series-congr`) -/
theorem countingZetaSeries_congr {c c' : ℕ → ℕ} (h : ∀ n, n ≠ 0 → c n = c' n) :
    countingZetaSeries c = countingZetaSeries c' := by
  have hlog : countingLogSeries c = countingLogSeries c' := by
    ext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, h n hn]
  rw [countingZetaSeries, countingZetaSeries, hlog]

end

end PowerSeries

end
