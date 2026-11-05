/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Iterating an adjoint coefficient comparison through a flat extension

Source: Stacks Project, Tags 00HD and 05G3.
(blueprint: lem-pc-flat-iterated-scalar-extension-homology-square). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

end ModuleCat
