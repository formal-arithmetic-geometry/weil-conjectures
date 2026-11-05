/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # A finite type algebra as a compatible ring system

Source: the finite-generator construction underlying Stacks Project, Algebra, Tag 00QV.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace RingHom

-- A named construction keeps the stage ring structures shared in conversion checks.

end RingHom
