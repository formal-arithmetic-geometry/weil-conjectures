/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Tensor comparison for affine tilde stalk modules

Source: Stacks Project, Schemes, Tag 01HV, and More on Algebra, Tag 06Y1.
(blueprint: lem-pc-affine-tilde-stalk-tensor-comparison).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

end AlgebraicGeometry
