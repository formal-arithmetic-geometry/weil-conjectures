/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.LineCounitComparison

/-! # Comparison of the independently normalized ordered integration

Source: blueprint sk-prop-an, lem-amb-affine-space-top-trace, proof paragraphs 2--3;
Stacks 099R, 09AF, and 0B65.
(blueprint: lem-pur-ordered-integration-comparison).
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

attribute [local implicit_reducible] Etale.cartierAbelianPro Etale.cartierAbelianEtale
attribute [local implicit_reducible] affineTraceTower
attribute [local implicit_reducible] affineTraceLineCompactification Etale.affineTraceOpenLeft

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
