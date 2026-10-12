/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing
import Sheaf.Paper.OpenCurveEtaleLerayLowDegree

/-!
# Direct-image cohomology of the multiplicative group on an open curve

Source: Stacks Project, Section 59.68, discussion preceding Tag 03RM
(blueprint: lem-sc-open-curve-gm-direct-image-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Removing finitely many closed points from a proper smooth connected curve over an
algebraically closed field gives the natural Leray comparison isomorphism in degrees at most
two. Source: Stacks Project, Section 59.68, discussion preceding Tag 03RM
(blueprint: lem-sc-open-curve-gm-direct-image-cohomology).

Proof: first use `lem-sc-open-curve-boundary-higher-direct-image-vanishing`. At a geometric
point in the open, the immersion is locally an isomorphism. At a removed closed point, the
higher direct-image stalk is the cohomology of the fraction field of the strict henselization
of the local DVR. Hilbert 90 kills degree one and Brauer vanishing kills degree two.
Next apply `lem-sc-open-curve-etale-leray-low-degree`: in the Leray spectral sequence the
rows for higher direct images one and two vanish, making the edge map an isomorphism in
degrees zero, one and two. The edge map here is pullback followed by the adjunction counit,
as identified in `AlgebraicGeometry.Etale.map_counit_cohomologyMap`. -/
theorem bijective_openCurve_gm_directImage_cohomology
    {k : Type u} [Field k] [IsAlgClosed k] {Cbar C : Scheme.{u}}
    [Cbar.Over (Spec (.of k))] [IsConnectedCurve (Cbar ↘ Spec (.of k))]
    [Smooth (Cbar ↘ Spec (.of k))] [IsProper (Cbar ↘ Spec (.of k))]
    (S : Finset Cbar) (hS : ∀ p ∈ S, IsClosed ({p} : Set Cbar))
    (j : C ⟶ Cbar) [IsOpenImmersion j]
    (hj : Set.range j.base = (↑S : Set Cbar)ᶜ) (q : ℕ) (hq : q ≤ 2) :
    Function.Bijective
      (fun x : Sheaf.H ((lowerStar AddCommGrpCat.{u + 1} j).obj C.gmSheaf) q ↦
        Sheaf.H.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).counit.app C.gmSheaf) q
          (cohomologyMap j _ q x)) := by
  sorry

end AlgebraicGeometry.Etale
