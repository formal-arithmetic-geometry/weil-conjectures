/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitZero
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitSuccessor
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Ordinary-counit normalization of ordered tensor integration
Source: projection-purity agreement, final paragraph, ordered counit calculation.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local semireducible] ordinarySourceObject
attribute [local implicit_reducible] ordinarySourceObject
  Etale.derivedTensorRight Etale.derivedTensorRightFunctor Etale.rightDerivedLowerShriek
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  ordinaryLower sourceEtale etaleCategory proCategory

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
