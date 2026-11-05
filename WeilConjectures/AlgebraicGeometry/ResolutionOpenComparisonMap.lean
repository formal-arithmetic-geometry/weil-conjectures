/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # The fixed untwisted comparison

Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: def-pc-resolution-open-comparison-map). -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
noncomputable section

end
end AlgebraicGeometry.Scheme.Modules
