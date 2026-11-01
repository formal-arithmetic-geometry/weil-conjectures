/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationContraction
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedTransposeCounit
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedFirstLineCounit

/-! # Successor calculation for the ordered integration transpose

Source: current blueprint, projection-purity agreement, final paragraph; the expanded
ordered-transpose proof, Steps 3--7.
(blueprint: lem-pur-affine-ordered-integration-successor).
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
attribute [local implicit_reducible] compactification proCategory etaleCategory
attribute [local implicit_reducible] rightDerivedLowerShriek
attribute [local irreducible] rightDerivedUpperShriekHomEquiv
  rightDerivedUpperShriekCounit

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
