/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeBoundaryAnalyticComparison
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeMiddleTensorPowerEigenvalue
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeTensorPunctualWeights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius

/-! # Boundary semicontinuity of punctual weights

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/_section.md
and sk-p-real-semi.proof.md, paragraphs 1–7 (blueprint: sk-p-real-semi).

The middle image is the ordinary direct image of the actual condensed module,
with its canonical Frobenius base-change Weil structure. The bound is punctual.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2

private theorem middleWeilImage_hasPunctualWeightsAtMost_add_two
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {U₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (ι : PadicAlgCl l →+* ℂ) (a : ℝ)
    (ha : HasPunctualWeightsAtMost D l U₀ M ι a) :
    HasPunctualWeightsAtMost D l X₀ (middleWeilImage D l j₀ M) ι (a + 2) := by
  intro x i hi α hα
  obtain ⟨N, C, L, hidentity, hdisc⟩ :=
    middleLocalFactor_analyticComparison D l hl j₀ M hM ι a ha x i hi
  have hnonzero (z : ℂ) (hz : ‖z‖ < (D.q : ℝ) ^ (-(a / 2 + 1))) :
      (middleLocalFactor D l hl j₀ M hM x i hi ι).eval z ≠ 0 := by
    obtain ⟨hL, hC, hsum⟩ := hdisc z hz
    exact PowerSeries.boundary_polynomial_ne_zero _ N C L z hidentity hL hC hsum
  obtain ⟨hd, hcard⟩ := closedPoint_cardinality D x
  have hq : 1 < D.q := by
    rw [← D.card_base]
    exact (Finite.one_lt_card_iff_nontrivial (α := D.k₀)).mpr inferInstance
  have hα0 : α.down ≠ 0 := by
    intro hz
    exact eigenvalue_ne_zero D l j₀ M x i hi α hα (by
      apply ULift.ext
      exact hz)
  have hbound := PowerSeries.boundary_weight_le_add_two_of_no_zero
    ι D.q _ hq hd α.down hα0 a (middleLocalFactor D l hl j₀ M hM x i hi ι)
    (middleLocalFactor_factor D l hl j₀ M hM x i hi ι α hα) hnonzero
  rwa [← hcard] at hbound

/-- Ordinary middle extension preserves a punctual upper bound at every closed point.
Source: latest blueprint, sk-p-real-semi, statement and complete proof
(blueprint: sk-p-real-semi).

Proof: (1) Smooth geometrically connected curves are geometrically integral and
Noetherian; the complement of a dense open is a finite set of closed points.
(2) At a missing point choose an affine neighbourhood avoiding the other missing
points on which that point is a principal effective Cartier divisor. Its punctured
open is affine too. Ordinary direct image commutes with this open restriction,
including its Weil map, so this replacement preserves the boundary operator.
(3) The Euler product on the open has logarithm sum c_n T^n/n, where c_n is the
sum over d dividing n of d times the local trace of F_x^(n/d), over points of degree d.
Coefficientwise finiteness justifies this formal exponential identity.
(4) The punctual bound and trace-of-powers formula bound each trace by r q^(na/2).
The affine point count bounds the weighted number of points by D q^n. Thus
|c_n| is at most r D (q^(a/2+1))^n, and the formal exponential evaluates to a
nonzero function f throughout |z| < R = q^(-a/2-1).
(5) The boundary localization sequence gives H_c^0(X,j_*F)=0 and identifies
H_c^2(X,j_*F) with H_c^2(U,F). The top-cohomology bound makes its determinant
denominator D_X nonzero on that disc; the trace formula gives L_X=N_X/D_X.
(6) Let B be the product of the boundary local determinant polynomials with
T replaced by T^d(s). Splitting the Euler product gives B N_X = D_X L_U.
Evaluating this identity on the disc gives B(z) N_X(z)=D_X(z) f(z), a nonzero
right side. Thus B has no zero there, and a boundary eigenvalue alpha satisfies
|iota(alpha)|^2 ≤ q_s^(a+2), by taking a d(s)-th root of iota(alpha) inverse.
(7) Apply this estimate to every positive tensor power. The inertia-invariant
boundary stalk contains a nonzero eigenvector v; v tensor k is nonzero, invariant,
and has eigenvalue alpha^k. Hence |iota(alpha)|^(2k) ≤ q_s^(ka+2) for every k.
Taking roots and letting k tend to infinity gives the bound a. On the open the
bound is the hypothesis. The zero sheaf and empty boundary need no exception. -/
theorem middleWeilImage_hasPunctualWeightsAtMost
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    {U₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (_hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (ι : PadicAlgCl l →+* ℂ) (a : ℝ)
    (_ha : HasPunctualWeightsAtMost D l U₀ M ι a) :
    HasPunctualWeightsAtMost D l X₀ (middleWeilImage D l j₀ M) ι a := by
  have : IsSeparated U₀.hom := by
    rw [← j₀.w]
    infer_instance
  intro x i hi α hα
  apply weight_le_of_all_pow_weight_le ι (Nat.card (X₀.left.residueField x.val))
    α.down a 2
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hLis := (positiveWeilTensorPower_properties D l U₀ M _hM n).1
  have hweights := positiveWeilTensorPower_hasPunctualWeightsAtMost
    D l _hl U₀ M _hM ι a _ha n
  have heigen := middleWeilImage_tensorPower_hasEigenvalue
    D l _hl j₀ M _hM x i hi α hα n
  exact middleWeilImage_hasPunctualWeightsAtMost_add_two
    D l _hl j₀ _ hLis ι _ hweights x i hi _ heigen

end WeilConjectures.NativeL2
