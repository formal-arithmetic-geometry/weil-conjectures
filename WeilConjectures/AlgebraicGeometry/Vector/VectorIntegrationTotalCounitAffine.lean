/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationTotalCounit.VectorIntegrationTotalCounitMaps

/-! # Flattening an affine tower preserves its ordered counit

Source: vector-bundle purity proof, paragraph 2, the ordered affine counit calculation.
(blueprint: lem-pur-vector-integration-total-counit-affine).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek upperStar lowerStar
  leftDerivedUpperStarComp Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

end AlgebraicGeometry.Etale
