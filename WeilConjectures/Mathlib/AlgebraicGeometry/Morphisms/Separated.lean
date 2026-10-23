/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Separated morphisms and the over category

`AlgebraicGeometry.isSeparated_overMk_hom` transfers separatedness from `f : X ⟶ S` to the
structure morphism of the object `Over.mk f` of `Over S`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The structure morphism of `Over.mk f` is separated if `f` is. -/
instance isSeparated_overMk_hom {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    IsSeparated (Over.mk f).hom :=
  ‹_›

end AlgebraicGeometry
