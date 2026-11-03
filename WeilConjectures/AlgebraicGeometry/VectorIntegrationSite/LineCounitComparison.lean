/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectionIntegration
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveCoefficient
import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.SupportedProjectiveChernComparison
import all WeilConjectures.AlgebraicGeometry.Open.OpenSiteEvaluationCounit
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin

/-! # Site comparison of a normalized affine-line counit

Source: blueprint sk-prop-an, affine-space top trace, proof paragraphs 1--2;
Stacks 099R, 09AF, 0B65, and 0GL1.
(blueprint: lem-pur-line-counit-comparison).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] Etale.affineTraceOpenLeft
attribute [local implicit_reducible] affineTraceLineCompactification affineTraceTower
attribute [local implicit_reducible] Etale.cartierAbelianPro Etale.cartierAbelianEtale

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
