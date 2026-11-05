/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenDerivedStalkIso
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Underived tensor restriction and its derived target transport

Source: Stacks Project, Tags 0D5U and 0D5S, exact restriction and composition.
(blueprint: def-pc-open-restricted-tensor-complex-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

end AlgebraicGeometry.SingleComplexBaseChange
