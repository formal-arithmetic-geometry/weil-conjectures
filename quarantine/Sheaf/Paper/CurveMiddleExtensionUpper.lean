/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Category
public import Sheaf.Paper.CurveWeilMiddleExtension
public import Sheaf.Paper.OrdinaryCompactWeilCohomology
import WeilConjectures.AlgebraicGeometry.Curve.AffineCore
import Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds
import WeilConjectures.DeligneLaumon.AffineLine.DegreeOne
import WeilConjectures.WeilSheaf.FourierTateTwist
import WeilConjectures.WeilSheaf.Stalk
import WeilConjectures.DeligneLaumon.AffineLine.LocalDuality
import Sheaf.Paper.LisseDenseOpenRecovery
import Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient
import Sheaf.DeligneLaumon.Reduction.AffineCurveUpper
import Sheaf.Paper.FiniteBoundaryWeights
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary
import WeilConjectures.WeilSheaf.Cohomology

/-!
# The upper weight bound for ordinary middle extensions on curves

Source: Weil blueprint main-20261015, sec-deligne-laumon-a1/sk-thm-dl-a1-upper,
proposition prop-a1-middle-extension-curve-upper
(blueprint: prop-a1-middle-extension-curve-upper).

The middle extension is ordinary sheaf direct image. Compactly supported cohomology
retains its canonical geometric Frobenius, and the weight bound is relative to #k₀.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

/-- Let j : U₀ ↪ C₀ be a dense open immersion of smooth geometrically connected curves.
For a lisse Weil sheaf punctually ι-pure of weight w, the compactly supported cohomology
of its ordinary middle extension has weights at most w + r in every integer degree r.

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-thm-dl-a1-upper,
prop-a1-middle-extension-curve-upper
(blueprint: prop-a1-middle-extension-curve-upper).

Proof: Choose a dense affine core V₀ of U₀ using lem-a1-affine-core-of-curve.
Its complement in C₀ is finite. By lem-a1-lisse-middle-extension, restriction of F to
V₀ recovers F by ordinary direct image on U₀; transitivity identifies its middle
extension to C₀ with j_*F. If F has rank zero, it and all the groups in question
vanish, so every bound holds. Otherwise apply thm-a1-affine-curve-upper to the
restriction, obtaining the bounds w+r and vanishing outside degrees 0, 1, 2.
By lem-wf-boundary-semicontinuity and lem-wf-boundary-stalk-invariants, boundary
stalks have weights at most w. The lemmas lem-a1-finite-boundary-weights and
lem-a1-finite-boundary-cohomology give a boundary group of weights at most w
concentrated in degree zero. The localization sequence prop-a1-curve-boundary-sequence
expresses H_c^0(C,j_*F) as an extension of H_c^0(V,F) by a subobject of the boundary
group, H_c^1(C,j_*F) as a quotient of H_c^1(V,F), and identifies the groups in degrees
at least two with those on V. It also gives vanishing in negative degrees and above
two. Apply lem-a1-subquotient-extension-bounds and lem-a1-extension-bounds to obtain
the stated upper bound in each degree. -/
theorem hasWeightsAtMost_compactlySupportedCohomology_curveMiddleExtension
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {U C : Scheme.{u}} [U.Over (Spec (.of k₀))] [C.Over (Spec (.of k₀))]
    [IsCurve (U ↘ Spec (.of k₀))] [IsCurve (C ↘ Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k₀))]
    [GeometricallyConnected (U ↘ Spec (.of k₀))]
    [GeometricallyConnected (C ↘ Spec (.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [j.IsOver (Spec (.of k₀))]
    (hj : DenseRange j.base) (ι : PadicAlgCl l ≃+* ℂ)
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) (w : ℝ)
    (hw : F.IsPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) w) (r : ℤ) :
    FrobeniusModule.HasWeightsAtMostOver k₀ (ι : PadicAlgCl l →+* ℂ)
      (ordinaryCompactWeilSheafCohomology ((curveWeilMiddleExtension j).obj F) r).2
      (w + (r : ℝ)) := by
  sorry

end AlgebraicGeometry.WeilSheaf
