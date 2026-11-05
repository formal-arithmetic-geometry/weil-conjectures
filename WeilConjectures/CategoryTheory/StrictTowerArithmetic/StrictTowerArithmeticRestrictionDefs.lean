/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! Definitions for canonical arithmetic restriction of strict derived towers. -/

@[expose] public section

set_option autoImplicit false

universe a b w uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.StrictTowerArithmetic

end CategoryTheory.StrictTowerArithmetic
