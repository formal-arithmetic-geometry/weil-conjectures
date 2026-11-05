/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Sheaf

/-! # Underlying modules of commutative algebra sheaves

Source: Stacks Project, Sheaves, Section 009E and Lemma 0087; Modules, Lemma 01AH
(blueprint: def-weil-pbc-ringed-space-algebra-module).
-/

@[expose] public section

universe uA

open CategoryTheory TopologicalSpace

namespace CategoryTheory

variable {X : Type uA} [TopologicalSpace X]

local notation "J" => Opens.grothendieckTopology X

end CategoryTheory
