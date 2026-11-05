/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictionStalkSquare

/-! # Open restriction of the tensor-pullback adjunction unit

Source: Stacks Project, Tags 0096 and 0098.
(blueprint: lem-pc-open-tensor-restriction-square-stalk-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

section
attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.pushforward
  Scheme.Modules.pushforwardComp Scheme.Modules.pushforwardCongr
  openTensorRestrictionIso openTensorRestrictionSquareIso

end

end AlgebraicGeometry.SingleComplexBaseChange
