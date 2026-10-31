/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitNormalization
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionOrientationMapExt
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitIsIso
import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionRankZeroAffineNormalization
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionComparisonIsoPasting

/-! # Finite-ring orientations along bundle zero sections

The canonical integration mate constructs the orientation. Its affine normalization
and equality detection on affine frames give existence and uniqueness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

end AlgebraicGeometry.Etale
