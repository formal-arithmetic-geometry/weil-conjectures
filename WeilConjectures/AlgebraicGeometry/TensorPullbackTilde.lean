/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-!
# Pullback of associated modules on affine schemes

Source: Stacks Project, Schemes, Tag 01I9 (1), using Tags 01I7 and 01BJ
(blueprint: lem-weil-pbc-tilde-pullback-base-change).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry.Scheme.Modules
