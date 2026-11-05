/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.CategoryTheory.Filtration

/-!
# Filtrations of objects in an abelian category

Source: Stacks Project, Homology, Definition 12.19.1 (Tag 0121)
(blueprint: def-sp-filtration).
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- (blueprint: def-sp-filtration) A decreasing filtration of `A` is an integer-indexed
family of subobjects, decreasing as the integer increases (Stacks, Tag 0121). -/
structure PBCDecreasingFiltration (A : C) where
  step : ℤ → Subobject A
  antitone_step : Antitone step

namespace PBCFilteredObject

end PBCFilteredObject

namespace PBCDecreasingFiltration

end PBCDecreasingFiltration

end CategoryTheory
