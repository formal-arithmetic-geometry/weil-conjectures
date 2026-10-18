/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Positive products and radii of convergence

Source: literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-p-real-rankin/
lem-rp-positive-product-radius.md,
node lem-rp-positive-product-radius (blueprint: lem-rp-positive-product-radius).
-/

@[expose] public section

open scoped ENNReal NNReal BigOperators

namespace PowerSeries

universe u

/--
Source: literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-p-real-rankin/
lem-rp-positive-product-radius.md, node lem-rp-positive-product-radius
(blueprint: lem-rp-positive-product-radius).

For a degreewise locally finite family of nonnegative power series with constant term one,
if its coefficientwise product is the Taylor series at zero of a function holomorphic on the
open disc of radius `R`, each factor has radius at least `R`.  The proof compares every factor
coefficient with the corresponding nonnegative product coefficient, applies Taylor convergence
and the nonnegative summability comparison, and then uses finite polynomial-times-partial-sum
identities to prove the final zero-free assertion.

Proof (the five steps of the source DAG node):
1. Write the constant coefficient of every factor as one. In degree `n`, local finiteness
   supplies a finite set of factors; enlarge it to include the chosen factor `j`. The term
   selecting degree `n` from `j` and degree zero from all other factors is its coefficient.
   All other terms are nonnegative, so `0 ≤ a_{j,n} ≤ A_n`, and `A_0 = 1`.
2. Apply `lem-rp-taylor-sum-on-disc` (`Complex.hasSum_taylorSeries_on_eball`) at zero
   and at every real `0 ≤ t < R`. The Taylor coefficients are `A_n`. Taking real parts
   gives summability of the nonnegative real series with terms `A_n * t^n`.
3. Apply `lem-rp-nonnegative-summable-comparison` (`Summable.of_nonneg_of_le`) to
   `0 ≤ a_{j,n} * t^n ≤ A_n * t^n`. Thus each factor converges absolutely for every
   `0 ≤ t < R`; the radius definition of `d-real-series` gives the first conclusion.
   For `R = ∞` use all finite `t`; for `R = 0` the conclusion is automatic.
4. If `f j = P⁻¹`, expand the formal identity `P * f j = 1` coefficientwise. For
   `P = ∑ p_k T^k` of degree `d` and partial sums `s_N`, summing those identities gives
   `1 = ∑_{k=0}^d p_k z^k s_{N-k}(z)` whenever `N ≥ d`.
5. If `P(z) = 0` and `|z| < R`, subtract `P(z) * s_N(z) = 0`. The triangle inequality
   bounds one by a finite sum of tails of the convergent nonnegative series
   `∑ a_{j,n} |z|^n`. Each tail tends to zero as `N` increases, a contradiction.
   This also covers `P = 1` and `z = 0`.
-/
theorem positive_product_radius
    {J : Type u} (f : J → ℂ⟦X⟧)
    (hf : ∀ j, (f j).HasNonnegCoeffs)
    (hconst : ∀ j, PowerSeries.constantCoeff (f j) = 1)
    (F : ℂ⟦X⟧)
    (hlocal : ∀ n : ℕ, ∃ S : Finset J,
      (∀ (j : J) (k : ℕ), 1 ≤ k → k ≤ n →
        PowerSeries.coeff k (f j) ≠ 0 → j ∈ S) ∧
      PowerSeries.coeff n F = PowerSeries.coeff n (∏ j ∈ S, f j))
    (R : ℝ≥0∞) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h (Metric.eball 0 R))
    (hTaylor : ∀ n : ℕ,
      PowerSeries.coeff n F = (Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n h 0)
    : (∀ j : J, R ≤ (f j).radius) ∧
      (∀ (j : J) (P : Polynomial ℂ),
        f j = (P : ℂ⟦X⟧)⁻¹ → P.eval 0 = 1 →
          ∀ z ∈ Metric.eball 0 R, P.eval z ≠ 0) := by
  sorry

end PowerSeries

end
