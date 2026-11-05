/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Stalks commute with direct sums of sheaves of modules

Source: Stacks Project, Sheaves on Spaces, Section 6.29, Tag 009E, items (3) and (5)
(blueprint: lem-pc-stalk-direct-sums).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite DirectSum
open TopCat.Presheaf

namespace SheafOfModules

end SheafOfModules
