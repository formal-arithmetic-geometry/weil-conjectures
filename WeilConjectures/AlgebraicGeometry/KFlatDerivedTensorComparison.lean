/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.KFlat

/-! # Natural computation of derived tensor on K-flat first models

Source: Stacks Project, Tag 06YH, construction of the derived tensor product.
(blueprint: lem-pc-kflat-derived-tensor-comparison).
-/

@[expose] public section

universe u w vI uI vJ uJ

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
