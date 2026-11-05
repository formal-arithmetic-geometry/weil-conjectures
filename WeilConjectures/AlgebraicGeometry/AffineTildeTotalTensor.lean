/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Tilde and the unbounded total tensor complex

Source: Stacks Project, Tag 08DX, proof of the affine computation.
(blueprint: lem-pc-affine-tilde-total-tensor).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Both the global linear map and its sheaf extension are uniquely determined:
-- pure tensors generate the module tensor, and the tilde adjunction detects the extension.

end AlgebraicGeometry
