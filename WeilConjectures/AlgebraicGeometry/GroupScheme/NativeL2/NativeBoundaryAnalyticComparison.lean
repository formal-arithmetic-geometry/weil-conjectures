/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeMiddleLocalFactor
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealWeights
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius

/-! # Polynomial comparison for the native ordinary middle image

Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-semi/sk-p-real-semi.proof.md,
localization and the two L-functions, through the boundary-factor identity.
(blueprint: lem-wf-native-boundary-analytic-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures.NativeL2

/-- The local determinant participates in a polynomial-series identity whose right side
has a nonvanishing, absolutely convergent evaluation on the weight disc.
Source: latest blueprint, sk-p-real-semi.proof.md, paragraphs 1--6
(blueprint: lem-wf-native-boundary-analytic-comparison).

Proof: At a missing point shrink to an affine neighbourhood, avoiding the other missing
points, on which that point is a principal Cartier divisor. Its punctured open is affine.
Restriction of ordinary direct image identifies the actual stalk and its canonical Weil
operator with the original ones. Let L be the Euler series on the punctured open.
Expanding the local determinant logarithms gives c_n = sum over d dividing n of d times
sum over degree-d closed points of the trace of F_x^(n/d). A rank bound r, the punctual
weight bound and the affine point count give |c_n| <= r C q^(n(a/2+1)). The formal
exponential therefore converges absolutely and has nonzero sum throughout the stated disc.
The compactly supported degree-zero group of the ordinary middle image is zero: its
sections have finite support and vanish on a dense open of the connected lisse locus.
Localization identifies its degree-two group with that of the punctured open. Its
Frobenius eigenvalues have absolute value at most q^(a/2+1), so its determinant D has
no root on the disc. The trace formula gives L_X = N_X/D. Split the Euler factors
into the punctured open and finite boundary to obtain B N_X = D L. Take N to be N_X
multiplied by all boundary factors other than the specified one. These are actual
polynomials of the canonical stalk operators; no choice of their zero loci is used.
At a point on the original open, the direct-image counit identifies its stalk with the
original stalk. Its bound a implies that its determinant B has no zero on the larger
weight-a disc, and hence on the stated disc. Here take N=1, D=B and L=1.
The rank-zero case has all determinant polynomials and Euler series equal to one. -/
theorem middleLocalFactor_analyticComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {U₀ X₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [SmoothOfRelativeDimension 1 X₀.hom] [GeometricallyConnected X₀.hom]
    (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left] [IsDominant j₀.left]
    (M : WeilModule D l U₀)
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (ι : PadicAlgCl l →+* ℂ) (a : ℝ)
    (ha : HasPunctualWeightsAtMost D l U₀ M ι a)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    ∃ (N C : Polynomial ℂ) (L : PowerSeries ℂ),
      ((middleLocalFactor D l hl j₀ M hM x i hi ι * N : Polynomial ℂ) : PowerSeries ℂ) =
        (C : PowerSeries ℂ) * L ∧
      ∀ z : ℂ, ‖z‖ < (D.q : ℝ) ^ (-(a / 2 + 1)) →
        (Summable fun n : ℕ ↦ ‖PowerSeries.coeff n L * z ^ n‖) ∧
        C.eval z ≠ 0 ∧ (∑' n : ℕ, PowerSeries.coeff n L * z ^ n) ≠ 0 := by sorry

end WeilConjectures.NativeL2
