/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationNormalization
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationStepComparison

/-! # Contraction of the ordered coefficient evaluations

Source: projection-purity agreement, final paragraph, ordered integration.
(blueprint: lem-route-ordered-evaluation-contraction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
  etaleCategory proCategory sourceEtale

set_option maxHeartbeats 1600000 in
-- The source and counit comparisons carry large derived-category instances.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
