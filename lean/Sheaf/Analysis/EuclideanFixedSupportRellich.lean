/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

/-!
# Euclidean Rellich compactness with fixed compact support

Source: Demailly, Complex Analytic and Differential Geometry, VI §2, Rellich lemma (2.2),
printed p.289; Differential and pseudodifferential operators on manifolds, §2, Lemma 2.7,
pp.5–6, at orders one and zero (blueprint: lem-sfb-euclidean-fixed-support-rellich).
-/

@[expose] public section

open MeasureTheory Filter
set_option autoImplicit false

open scoped Topology ContDiff

namespace MeasureTheory

/-- A bounded sequence with square-integrable first weak derivatives and fixed compact support
has an `L²` convergent subsequence whose limit has the same almost-everywhere support.

Source: Demailly, Complex Analytic and Differential Geometry, VI §2 (2.2), printed p.289;
Differential and pseudodifferential operators on manifolds, §2, Lemma 2.7, pp.5–6, at `t = 1`
and `s = 0` (blueprint: lem-sfb-euclidean-fixed-support-rellich).

Proof plan:
1. If the target dimension is zero, use the zero function and identity subsequence. Otherwise
   choose a positive common energy bound `M`. Each scalar coordinate and its weak derivatives
   have energy at most `M`; the weak identities pass to coordinates and complexifications.
2. By `lem-sfb-fixed-support-fourier-lipschitz`, the scalar Fourier integrals have a common
   bound `vol(K)^(1/2) * sqrt(M)` and Lipschitz constant
   `2π * (∫ x in K, ‖x‖^2)^(1/2) * sqrt(M)`.
   By `lem-sfb-l1-l2-fourier-realization` these represent the isometric `L²` Fourier transform.
   Apply `lem-sfb-l2-weak-derivative-fourier-identity` to each first coordinate derivative.
   Squaring norms and summing gives `∫ ξ, (1 + 4π² * ‖ξ‖²) * |hₙ(ξ)|² ≤ M`.
3. Euclidean closed balls and the bounded complex disk are compact by
   `lem-sfb-finite-dimensional-normed-proper`. The common Lipschitz bound gives
   equicontinuity, so `lem-sfb-ascoli-compact-closure` and
   `lem-sfb-compact-metric-subsequence` give uniform convergence on each ball along a
   subsequence, also after any earlier extraction.
4. Choose nested increasing index maps `pⱼ = pⱼ₋₁ ∘ qⱼ` giving convergence on the radius-`j`
   ball. The diagonal map `nₖ = pₖ(k)` is strictly increasing since
   `pₖ₊₁(k+1) ≥ pₖ(k+1) > pₖ(k)`. For each fixed `j`, its tail samples the convergent
   `pⱼ` subsequence at indices tending to infinity, hence is uniformly Cauchy on that ball.
5. The squared Fourier difference outside the radius-`R` ball is at most
   `4M / (1 + 4π² * R²)`. Choose `R` so this is less than half the desired squared error.
   Inside the ball, its integral is at most the finite ball volume times the squared
   uniform difference, which is eventually less than the other half. Plancherel
   (`lem-sfb-l1-l2-fourier-realization`) makes the scalar subsequence `L²` Cauchy.
6. Extract successively over the finitely many target coordinates. The squared vector
   `L²` norm is the sum of the squared coordinate `L²` norms, so the final subsequence
   is Cauchy. Completeness, the order-zero case of
   `lem-sfb-euclidean-sobolev-graph-mollification`, gives a limit `f`. Off `K`, the
   squared norm of `f` has integral at most the squared `L²` error against each term,
   tending to zero. Thus `f` vanishes almost everywhere outside `K`. -/
theorem euclidean_fixed_support_rellich
    (m r : ℕ) (hm : 1 ≤ m) (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K)
    (f : ℕ → Lp (EuclideanSpace ℝ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (d : ℕ → Fin m → Lp (EuclideanSpace ℝ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (hsupport : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      x ∉ K → f n x = 0)
    (hweak : ∀ (n : ℕ) (j : Fin m) (φ : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x, φ x • d n j x) =
          -(∫ x, (fderiv ℝ φ x (EuclideanSpace.single j 1)) • f n x))
    (hbounded : ∃ M : ℝ, ∀ n : ℕ, ‖f n‖ ^ 2 + ∑ j : Fin m, ‖d n j‖ ^ 2 ≤ M) :
    ∃ (a : ℕ → ℕ) (g : Lp (EuclideanSpace ℝ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin m)))),
      StrictMono a ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin m))), x ∉ K → g x = 0) ∧
        Tendsto (fun k : ℕ => ‖f (a k) - g‖) atTop (𝓝 0) := by
  sorry

end MeasureTheory
