/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ResolutionOpenComparisonMap
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-! # Restriction naturality of raw section cohomology

Source: Stacks Project, Tags 01E1, 01E2 and 01E4.
(blueprint: lem-pc-resolution-open-restriction-natural). -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

end AlgebraicGeometry.Scheme.Modules
