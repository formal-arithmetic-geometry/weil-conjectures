/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.OpenCoverAdjunctionTriangle

/-! # Hom identifications for the open-cover triangle

Source: Stacks Project, Tags 08BU, 08BT and 08BW.
(blueprint: lem-sc-open-hom-triangle-realization).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

noncomputable section

namespace SheafOfModules

-- The original existential binder eN is used only through its asserted existence.

end SheafOfModules
