/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-! # The module tensor pullback square on stalks

Source: Stacks Project, Modules, Tags 01CD and 01CB; Sheaves, Tag 0098.
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
