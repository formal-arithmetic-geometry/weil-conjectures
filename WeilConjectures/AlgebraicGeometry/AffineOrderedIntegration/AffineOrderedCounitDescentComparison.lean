/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
public import WeilConjectures.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization.OrdinaryAffineCounitTensorMaps
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Equality of the canonical ordered source descents -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
open CategoryTheory.Limits
open scoped CategoryTheory.Functor

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1 Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3 Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5 Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7 Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9 Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11 Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory.singleFunctors

attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
