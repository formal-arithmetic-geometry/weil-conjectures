/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetRowReassembly
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate

/-! # Ordered horizontal faces of a single principal-open subset

Source: Stacks Project, Tags 08C1, 08C0, and 01FG.
(blueprint: lem-sc-principal-open-cech-subset-horizontal-faces).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance] Classical.propDecidable

end AlgebraicGeometry
