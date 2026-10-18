/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Restricted nonarchimedean series: evaluation, products, and substitution

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-log,
lem-wf-deep-principal-unit-log.proof.md, paragraph 3, with the explicit coefficient criterion
of Q153 (blueprint: lem-wf-nonarchimedean-series-substitution).

`PowerSeries.IsRestricted` is the weighted coefficient-decay condition. Evaluation is written
as a `tsum`, and formal composition uses Mathlib's `PowerSeries.subst`. The sigma type of
positive tuples includes the unique empty tuple at length zero.
-/

@[expose] public section

universe u

open scoped BigOperators

namespace PowerSeries

/-- Evaluation converges on the entire closed disc. Source: blueprint main-20261015,
lem-wf-deep-principal-unit-log.proof.md, paragraph 3, coefficient criterion step 1
(blueprint: lem-wf-nonarchimedean-series-substitution).

Proof: The term norms are bounded by `‖coeff m H‖ * ρ ^ m`, which tend to zero.
The ultrametric cofinite summability criterion from lem-wf-ultrametric-family-summability
then gives convergence, using completeness, including for a trivial absolute value. -/
theorem nonarchimedean_restricted_eval {K : Type u} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (ρ : ℝ) (hρ : 0 < ρ)
    (H : PowerSeries K) (hH : IsRestricted ρ H) (x : K) (hx : ‖x‖ ≤ ρ) :
    Summable (fun m : ℕ ↦ coeff m H * x ^ m) := by
  sorry

/-- Cauchy products preserve restriction and commute with evaluation. Source: blueprint
main-20261015, lem-wf-deep-principal-unit-log.proof.md, paragraph 3, coefficient criterion
steps 2 and 3 (blueprint: lem-wf-nonarchimedean-series-substitution).

Proof: Put `U i = ‖coeff i H‖ * ρ ^ i` and `V j = ‖coeff j J‖ * ρ ^ j`. Choose a common
bound `M ≥ 1`. For any positive epsilon, choose `N` such that both sequences are smaller
than epsilon/M past N. At degree at least 2N, each Cauchy pair has an index at least N.
The ultrametric inequality for the finite coefficient sum gives weighted coefficient decay
(as in def-weil-formal-power-series). For evaluation, step 1 gives summability of both
factor families. The lemma lem-wf-nonarchimedean-summable-products gives the double family
with sum the product of evaluations. Regroup it by the sum of the two indices using
lem-wf-summable-family-regrouping; its finite fibers give the Cauchy coefficients. -/
theorem nonarchimedean_restricted_mul {K : Type u} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (ρ : ℝ) (hρ : 0 < ρ)
    (H J : PowerSeries K) (hH : IsRestricted ρ H) (hJ : IsRestricted ρ J) :
    IsRestricted ρ (H * J) ∧
      ∀ (x : K), ‖x‖ ≤ ρ →
        (∑' k : ℕ, coeff k (H * J) * x ^ k) =
          (∑' i : ℕ, coeff i H * x ^ i) * (∑' j : ℕ, coeff j J * x ^ j) := by
  sorry

/-- Substitution preserves restriction, commutes with evaluation, and admits both length
and degree regroupings of its summable monomial family. Source: blueprint main-20261015,
lem-wf-deep-principal-unit-log.proof.md, paragraph 3, coefficient criterion steps 1 and 4--8
(blueprint: lem-wf-nonarchimedean-series-substitution).

Proof: Step 1 bounds every inner evaluation term by `B m = ‖coeff m G‖ * ρ ^ m ≤ s`;
ultrametric summability and its norm bound give `‖G(x)‖ ≤ s`. The outer evaluation terms
are bounded by `A n = ‖coeff n F‖ * s ^ n`, which tend to zero. Step 4 expands powers
using the Cauchy formula of def-weil-formal-power-series: the composition coefficient at
k is the finite sum over positive tuples of total degree k. Positivity forces their
length to be at most k; at length zero the empty tuple contributes only at degree zero.
Step 5 bounds a weighted tuple term by `A n`. For epsilon positive, choose N with
`A n < epsilon` for n at least N. For each positive n below N with nonzero outer
coefficient, choose a cutoff using `B m → 0` so that one coordinate beyond the cutoff
makes the whole product less than epsilon, bounding its other n-1 coordinates by s.
Zero outer coefficients contribute nothing; the remaining tuples form finitely many
finite boxes, together with the empty tuple. Step 6 takes the degree beyond all these
exceptions; the finite coefficient formula and ultrametric inequality prove restriction
of the composition without requiring ρ in the value group. Step 7 applies
lem-wf-ultrametric-family-summability to the evaluated tuple family, and applies
lem-wf-summable-family-regrouping to its length and degree maps. Step 8 identifies each
length-n sum as `coeff n F * G(x)^n` by induction, using
lem-wf-nonarchimedean-summable-products and the bijection splitting off a tuple's last
entry. The zero-length product is 1. The degree sums are the composition coefficients,
so the two regroupings prove the evaluation identity and the stated term bound. -/
theorem nonarchimedean_restricted_subst {K : Type u} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (ρ s : ℝ) (hρ : 0 < ρ) (hs : 0 < s)
    (F G : PowerSeries K) (hG₀ : constantCoeff G = 0)
    (hG : IsRestricted ρ G)
    (hbound : ∀ m : ℕ+, ‖coeff (m : ℕ) G‖ * ρ ^ (m : ℕ) ≤ s)
    (hF : IsRestricted s F) :
    IsRestricted ρ (F.subst G) ∧
      ∀ (x : K), ‖x‖ ≤ ρ →
        ‖∑' m : ℕ, coeff m G * x ^ m‖ ≤ s ∧
        (∑' k : ℕ, coeff k (F.subst G) * x ^ k) =
          (∑' n : ℕ, coeff n F * (∑' m : ℕ, coeff m G * x ^ m) ^ n) ∧
        HasSum
          (fun α : (Σ n : ℕ, Fin n → ℕ+) ↦
            coeff α.1 F * ∏ j : Fin α.1, (coeff (α.2 j : ℕ) G * x ^ (α.2 j : ℕ)))
          (∑' k : ℕ, coeff k (F.subst G) * x ^ k) ∧
        HasSum
          (fun n : ℕ ↦ ∑' m : Fin n → ℕ+,
            coeff n F * ∏ j : Fin n, (coeff (m j : ℕ) G * x ^ (m j : ℕ)))
          (∑' k : ℕ, coeff k (F.subst G) * x ^ k) ∧
        HasSum
          (fun k : ℕ ↦ ∑' α :
              {α : (Σ n : ℕ, Fin n → ℕ+) // (∑ j : Fin α.1, (α.2 j : ℕ)) = k},
            coeff α.1.1 F *
              ∏ j : Fin α.1.1, (coeff (α.1.2 j : ℕ) G * x ^ (α.1.2 j : ℕ)))
          (∑' k : ℕ, coeff k (F.subst G) * x ^ k) ∧
        ∀ α : (Σ n : ℕ, Fin n → ℕ+),
          ‖coeff α.1 F *
              ∏ j : Fin α.1, (coeff (α.2 j : ℕ) G * x ^ (α.2 j : ℕ))‖ ≤
            ‖coeff α.1 F‖ * s ^ α.1 := by
  sorry

end PowerSeries
