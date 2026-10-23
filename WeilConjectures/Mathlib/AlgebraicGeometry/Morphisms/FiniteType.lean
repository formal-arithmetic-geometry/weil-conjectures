/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Morphisms locally of finite type and the over category

`AlgebraicGeometry.locallyOfFiniteType_overMk_hom` transfers the property of being locally of
finite type from `f : X ⟶ S` to the structure morphism of the object `Over.mk f` of `Over S`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The structure morphism of `Over.mk f` is locally of finite type if `f` is. -/
instance locallyOfFiniteType_overMk_hom {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (Over.mk f).hom :=
  ‹_›

end AlgebraicGeometry
