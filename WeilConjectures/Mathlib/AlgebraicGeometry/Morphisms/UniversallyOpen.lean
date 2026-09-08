/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Surjectivity of universally open and closed morphisms

A morphism of schemes that is both universally open and universally closed has clopen image, so
it is surjective as soon as its source is nonempty and its target is preconnected.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A universally open and universally closed morphism with nonempty source and preconnected
target is surjective, since its image is clopen and nonempty. -/
lemma surjective_of_universallyOpen_of_universallyClosed [UniversallyOpen f]
    [UniversallyClosed f] [Nonempty X] [PreconnectedSpace Y] : Surjective f :=
  ⟨Set.range_eq_univ.mp <| IsClopen.eq_univ
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩ (Set.range_nonempty _)⟩

end AlgebraicGeometry
