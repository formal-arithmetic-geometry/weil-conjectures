/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialInput
public import Mathlib.Algebra.Homology.Monoidal

/-! # Explicit Alexander--Whitney components

Source: Banerjee, Tensor Structure on Smooth Motives, §1.1.4, p. 16.
(blueprint: def-sc-module-cup-aw-components).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicTopology Simplicial

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

end
end AlgebraicGeometry.Scheme.Modules
