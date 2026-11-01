/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationTotalCounit.VectorIntegrationTotalCounitMaps
public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationOverlapChartPrefix

/-! # Exchange for the flattened simultaneous bundle chart

This comparison stops before any affine trace counit is applied.
(blueprint: lem-pur-vector-integration-total-counit-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek upperStar lowerStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme
  leftDerivedUpperStarComp leftDerivedUpperStarIsoMapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

end AlgebraicGeometry.Etale
