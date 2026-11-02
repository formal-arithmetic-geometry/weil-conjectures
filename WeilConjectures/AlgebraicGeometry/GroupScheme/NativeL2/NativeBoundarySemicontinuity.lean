/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

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
  sorry

end WeilConjectures.NativeL2
