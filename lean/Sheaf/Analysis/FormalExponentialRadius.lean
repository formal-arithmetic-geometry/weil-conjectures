/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The convergence radius of a formal exponential

Source: Weil conjectures blueprint, main-20261015, chapter `sec-deligne-laumon-a1`,
unit `sk-l-dl-a1-energy`, proof, last paragraph
(blueprint: lem-dl-a1-formal-exponential-radius).
-/

@[expose] public section

namespace PowerSeries

/-- Source: Weil conjectures blueprint, main-20261015, `sk-l-dl-a1-energy`, proof,
last paragraph (blueprint: lem-dl-a1-formal-exponential-radius).
The formal exponential of a complex power series with zero constant coefficient has
convergence radius at least that of the original series. Here `subst U (exp ℂ)` is the
coefficientwise finite series `∑ r, U ^ r / r!`, using the existing formal substitution.

Proof: fix a nonnegative real radius `ρ` admissible in the supremum defining `U.radius`,
and `0 ≤ t < ρ`. Set `a n = ‖coeff n U‖ * t ^ n`; its zeroth term is zero by `hU`.
This nonnegative sequence is summable with sum `S`. By
`lem-dl-a1-nonnegative-series-partial-sums` (i), each finite sum is at most `S`, and the
empty sum shows `0 ≤ S`.

Write `e n` for the coefficients of the formal exponential. Its constant coefficient is
one. For `n ≥ 1`, its finite coefficient formula and the complex norm triangle and product
identities give `‖e n‖ * t ^ n ≤ b n`, where `b n` is the sum, for `1 ≤ r ≤ n`, of `1 / r!`
times the sum of `∏ j, a (n j)` over positive integer tuples with total degree `n`.
Set `b 0 = 1`. All summands are nonnegative, including when `t = 0`.

Regrouping the finite sums through degree `N` bounds `∑ n ≤ N, b n` by
`∑ r ≤ N, (∑ j = 1..N, a j) ^ r / r!`: remove the total-degree restriction on the tuples
and expand the resulting finite product. This is at most `∑ r ≤ N, S ^ r / r!`.
The empty tuple contributes one for `r = 0`, so the same calculation covers `N = 0`.
By `lem-dl-a1-real-factorial-series-summable`, the factorial series is summable; clause (i)
of the partial-sum lemma bounds its finite sums by its sum `B`. Its terms are nonnegative,
so `0 ≤ B` also bounds the empty partial sum. Clause (ii) then proves summability of
`n ↦ ‖e n‖ * t ^ n`.

Thus every admissible `ρ` for `U` is admissible for its exponential. Inclusion of the
admissible sets gives the inequality of their suprema. Radius zero is automatic, and
unbounded admissible radii give the infinite-radius case. No boundary convergence is used. -/
theorem radius_le_radius_subst_exp (U : PowerSeries ℂ) (hU : constantCoeff U = 0) :
    U.radius ≤ PowerSeries.radius (subst U (exp ℂ)) := by
  sorry

end PowerSeries
