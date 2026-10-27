/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Sheaf.RingTheory.AffinoidQuotientNormTopology
import Sheaf.RingTheory.TateNormalizationLift

/-!
# Power-bounded elements are integral over the presentation unit ball

Source: Bosch, Lectures on Formal and Rigid Geometry (2008), Section 1.4,
Theorem 16, printed pp. 28--29, and Proposition 4(iii), printed p. 23
(blueprint: lem-trf-affinoid-powerbounded-integral).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace RestrictedSeries

/-- An element with bounded powers satisfies a positive-degree monic polynomial whose
coefficients lie in the image of the integral restricted series under the original
presentation. Membership in that image is expressed coefficient by coefficient:
each coefficient lifts through `q` to a restricted series with all coefficients in `V`.
Thus the polynomial is a polynomial over the subring `D` in the node, viewed in `C[X]`.
Continuity uses Gauss balls, not the coefficientwise topology of formal series.

Source: Bosch, Section 1.4, Theorem 16, printed pp. 28--29, and Proposition 4(iii),
printed p. 23 (blueprint: lem-trf-affinoid-powerbounded-integral).

Proof (the node's five steps):
1. Apply lem-trf-affinoid-quotient-norm-topology to this precise `q`. Equivalence
   of the quotient Gauss norm and the given Banach norm yields a bound `M ≥ 1`
   on the quotient norms of all powers of `c`.
2. Apply lem-trf-affinoid-supremum-seminorm-calculus: the supremum seminorm of
   `c` to the power `m` is at most `M`. If that seminorm were `1 + δ`, with `δ > 0`,
   the lower bound `(1 + δ)^m ≥ 1 + m * δ` would contradict boundedness.
   Hence the supremum seminorm of `c` is at most one.
3. Since `C` is nonzero, `ker q` is proper. Apply lem-trf-tate-normalization-lift
   to obtain an injection from a smaller Tate algebra into the original one whose
   composite with `q` is injective and finite. The quotient by `ker q` identifies
   with `C`, transporting the finite module generators.
4. Apply lem-trf-finite-affinoid-spectral-equation to this finite map and `c`.
   It gives a monic relation of degree at least one whose coefficients in the
   smaller Tate algebra have supremum seminorm at most one.
5. The contractivity and Tate-algebra equality in
   lem-trf-affinoid-supremum-seminorm-calculus show that the images of these
   coefficients in the original Tate algebra have Gauss norm at most one.
   Each series coefficient therefore belongs to `V`. Applying the original `q`
   gives coefficients in `D` and the required vanishing monic polynomial.
   The leading coefficient and the zero coefficients also lift, by constants.
   Neither reducedness nor algebraic closedness is used. -/
theorem affinoid_powerbounded_integral
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (V : ValuationSubring K) (hV : ∀ a : K, a ∈ V ↔ ‖a‖ ≤ 1)
    (r : ℕ) (C : Type v) [NormedCommRing C] [Nontrivial C]
    [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]
    (q : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+* C)
    (hscalar : q.comp (constants K r) = algebraMap K C)
    (hsurj : Function.Surjective q)
    (hcont : ∀ s, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t, MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
        (t.val - s.val) < δ → ‖q t - q s‖ < ε)
    (c : C) (hbounded : ∃ M : ℝ, ∀ m : ℕ, ‖c ^ m‖ ≤ M) :
    ∃ p : Polynomial C, p.Monic ∧ 0 < p.natDegree ∧ p.eval c = 0 ∧
      ∀ i : ℕ, ∃ s : (MvPowerSeries.IsRestricted.subring (R := K)
        (fun _ : Fin r ↦ (1 : ℝ))),
        (∀ ν : Fin r →₀ ℕ, MvPowerSeries.coeff ν s.val ∈ V) ∧ q s = p.coeff i := by
  sorry

end RestrictedSeries
