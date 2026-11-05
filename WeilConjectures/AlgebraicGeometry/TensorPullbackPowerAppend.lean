/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
import all WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit

/-! # Pullback of tensor-power concatenation with one factor

Source: Stacks Project, Tag 01CD, functorial pullback of tensor products.
(blueprint: lem-sc-tensor-pullback-power-append).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] tensorPullback boundaryPullbackComparison

end AlgebraicGeometry.Scheme.Modules
