/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData

/-! # Affine normalization of the coefficient-unit purity mate

Source: orientation-charts Step 4, expanded in the parent orientation node.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- The unit purity mate restricts on every affine linear frame to the prescribed
coordinate-tower adjunct.
Source: orientation-charts Step 4; parent proof Steps 3--5 and 9--10.
(blueprint: lem-trf-bundle-section-purity-unit-normalization).

Proof: the coefficient-first projection map at the unit, conjugated by the pullback
unit and tensor unitors, is the identity. For the proper factor this is the adjunction
triangle identity; for open extension it is the sheaf tensor-unit equation. The two
signed symmetries have sign one at the degree-zero coefficient unit. Its inverse,
specified by hp, therefore turns the displayed unit purity map into the adjunct of
the actual vector-bundle integration trace. On a frame, transpose through the open
compact-support exchange. Mate naturality identifies the resulting arrow with the
adjunct of the restricted trace. Integration normalization identifies that trace with
the affine coordinate-tower counit, and the section/pullback compositors identify its
coefficient source with bundleSectionChartCoefficient. Pulling back by the Cartesian
lift of the zero section gives precisely the defining normalization equation. This
uses arbitrary frames and the same normalized t,D throughout; their normalization
uniqueness removes any dependence on those choices. Empty bases and rank zero use
the same unit and adjunction equations; no nonzero coefficient is required. -/
theorem bundleSectionPurityUnit_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M))
    (hp : p.inv = vectorBundlePurityProjectionMap A N hA S d M (ordinaryFiniteUnit A S))
    (o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d)
    (ho : o.inv = (bundleSectionCoefficientIso A N hA S d M).inv ≫
      (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).map
        (bundleSectionPurityUnitMap N hN A hA S hS d M p)) :
    BundleSectionOrientationNormalization N hN A hA S hS d M o := by sorry

end AlgebraicGeometry.Etale
