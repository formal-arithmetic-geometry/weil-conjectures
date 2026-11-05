/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso

/-! # The representative of ordinary open tensor restriction

Source: Stacks Project, Tags 08HY and 08DW.
(blueprint: lem-pc-open-tensor-restriction-representative).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
open SingleComplexBaseChange

attribute [local irreducible] openPinnedTensorRestrictionIso

end AlgebraicGeometry
