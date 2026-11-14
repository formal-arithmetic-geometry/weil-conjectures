/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
import WeilConjectures.AlgebraicGeometry.AffineSpectrumUnitNormalization
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare

/-! # AffineSpectrumComparisonCancellation

## References

* Stacks Project, Tags 0D5S and 08HY
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The inverse unit component of the constructed spectrum equivalence, with its
pullback endpoints stated explicitly. No new choice of data is made (Stacks, Tag 0D5S). -/
noncomputable def affineSpectrumUnitInv (X : Scheme.{u}) [IsAffine X]
    (K : schemeDerivedCategory X) :
    (derivedPullback X.toSpecΓ).obj ((derivedPullback X.isoSpec.inv).obj K) ⟶ K :=
  (affineSpectrumInversePullbackEquivalence X).unitIso.inv.app K

/-- Forward and inverse spectrum pullback comparisons cancel the equivalence unit. -/
theorem affineSpectrum_comparison_cancellation
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X) (K : schemeDerivedCategory X) :
    (affineSpectrumForwardPullbackIso g').hom.app ((derivedPullback X.isoSpec.inv).obj K) ≫
      (derivedPullback X'.toSpecΓ).map
        ((affineSpectrumDerivedPullbackIso g').hom.app K) ≫
      affineSpectrumUnitInv X' ((derivedPullback g').obj K) =
    (derivedPullback g').map
      (affineSpectrumUnitInv X K) := by
  simp only [affineSpectrumUnitInv, affineSpectrum_unit_normalization]
  exact affineSpectrum_composition_unit_square g' K

end AlgebraicGeometry
