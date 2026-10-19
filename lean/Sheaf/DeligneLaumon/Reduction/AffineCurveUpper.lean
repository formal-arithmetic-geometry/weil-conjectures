/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Category
public import Sheaf.Paper.RealSheavesSetup
public import Sheaf.Paper.LisseAdicSheaves
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.OrdinaryCompactCohomology
public import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.Curve.FiniteMapAffineLine
import Sheaf.Paper.SfOpenClosedTriangleAllStages
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import Sheaf.WeilSheaf.FiniteBoundaryPositive
import WeilConjectures.DeligneLaumon.AffineLine.LocalDuality
import WeilConjectures.DeligneLaumon.AffineLine.DegreeOne
import WeilConjectures.WeilSheaf.FourierTateTwist
import WeilConjectures.WeilSheaf.Stalk
import WeilConjectures.DeligneLaumon.AffineLine.Upper
import Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient
import Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Sheaf.DeligneLaumon.Reduction.Composition
import Sheaf.Paper.AffineCurveHcZero
import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.FiniteBoundaryWeights
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineInfinityMap
import WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper

/-! # Affine compact-support upper bound

Source: literature/blueprint/master/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/
thm-a1-affine-curve-upper.md, node thm-a1-affine-curve-upper, order 2807
(blueprint: thm-a1-affine-curve-upper).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Compact-support upper bounds and the sharper endpoints for a lisse pure sheaf on a
smooth geometrically connected affine curve.

Source: blueprint main-20261015, sec-deligne-laumon-a1/sk-thm-dl-a1-upper,
thm-a1-affine-curve-upper.md, order 3151 (blueprint: thm-a1-affine-curve-upper).

Proof plan:
1. Lissity implies constructibility. Apply lem-a1-affine-hc0, lem-a1-affine-hc2-pure,
   and lem-zl-affine-curve-range for degree-zero vanishing, degree-two purity, and range.
2. By lem-a1-finite-map-curve choose a dense open enlargement j and a finite generically
   etale map g to the line. Lem-a1-reduction-composition identifies H_c^1 with that of
   K = g_* j_! F, compatibly with Frobenius. Lem-a1-reduction-lisse-pure gives a pure
   lisse restriction L on the complement W of the branch locus and boundary images.
3. Apply prop-sf-open-closed-triangle-all-stages and prop-functor-package to obtain
   the compact-support localization triangle. Its long exact sequence
   (lem-sf-derived-homology-long-exact) and lem-a1-finite-boundary-cohomology-positive
   give a Frobenius-equivariant surjection H_c^1(W,L) onto H_c^1(A,K).
4. Lem-a1-unramified-at-infinity, after a finite constant extension of degree m,
   supplies a pure lisse E on a dense open V of the line, unramified at infinity,
   with H_c^1(V,E) surjecting onto H_c^1(W,L). Frobenius becomes F^m and q becomes q^m.
5. Prop-a1-curve-boundary-sequence gives A_Z -> M -> N -> 0, with
   A_Z = H_c^0(Z,i^*v_*E), M = H_c^1(V,E), N = H_c^1(A,v_*E).
   Here v_* is ordinary sheaf direct image, not the derived direct image.
6. If E has rank zero all these boundary terms are zero. Otherwise apply
   lem-wf-boundary-semicontinuity at beta=w, then lem-a1-finite-boundary-weights,
   to bound A_Z by w.
7. Thm-a1-line-middle-extension-upper bounds N by w+1. The image of A_Z in M
   has bound w by lem-a1-subquotient-extension-bounds, hence also bound w+1.
   Apply lem-a1-extension-bounds to 0 -> im(A_Z) -> M -> N -> 0.
8. The surjections preserve the bound. P-linear-filtration turns it into an eigenvalue
   bound for F^m; lem-a1-weight-bound-constant-extension descends it to F. Over the
   algebraically closed coefficient field p-linear-triangular supplies an invariant
   flag whose one-dimensional quotients have their actual real weights at most w+1.
   The zero module uses the empty filtration.
9. Combine degree one with the endpoints: degree two has its one-step pure filtration,
   and every vanishing degree its empty filtration, giving the upper bound for every i.
-/
theorem compactlySupportedCohomology_affineCurve_upper
    [Fact (Nat.Prime (ringChar k₀))] (a : ℕ) (ha : 1 ≤ a)
    (hcard : Nat.card k₀ = ringChar k₀ ^ a)
    (ι : PadicAlgCl l ≃+* ℂ) {C₀ : Scheme.{u}}
    [C₀.Over (Spec (CommRingCat.of k₀))] [IsAffine C₀]
    [IsSeparated (C₀ ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C₀ ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C₀ ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C₀ ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l C₀) (hF : F.IsLisse) {w : ℝ}
    (hpure : F.IsPunctuallyPureOfWeight ι.toRingHom w) :
    (∀ i : ℤ,
      FrobeniusModule.IsMixedOfWeightsAtMost (ringChar k₀) a l ha
        (Ne.symm (Fact.out : ringChar k₀ ≠ l)) (PadicAlgCl l)
        (inferInstance : IsAlgClosure ℚ_[l] (PadicAlgCl l)) ι
        (F.compactlySupportedCohomology i) (w + i)) ∧
      Subsingleton (F.compactlySupportedCohomology 0).carrier ∧
      (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι.toRingHom (w + 2) ∧
      (∀ i : ℤ, i < 0 ∨ 2 < i →
        Subsingleton (F.compactlySupportedCohomology i).carrier) := by
  sorry

end AlgebraicGeometry.WeilSheaf
