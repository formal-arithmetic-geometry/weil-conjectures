/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Open restriction and extension of stalk scalars

Source: Stacks Project, Sheaves, Tag 0098; Cohomology, Tag 06YB.
(blueprint: lem-pc-open-restriction-stalk-extension-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TopologicalSpace Opposite

end AlgebraicGeometry
