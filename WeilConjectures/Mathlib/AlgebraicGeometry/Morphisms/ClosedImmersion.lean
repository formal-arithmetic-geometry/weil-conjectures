/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Open immersions that are universally closed

An open immersion whose underlying map is closed — for instance a proper one — is also a
closed immersion, and its range is a clopen subset of the target. Such a morphism is what is
classically called a *clopen immersion*: it identifies the source with a connected-component
union of the target.

## Main results

- `AlgebraicGeometry.IsClosedImmersion.of_isOpenImmersion` — an open immersion with closed
  range is a closed immersion;
- `AlgebraicGeometry.Scheme.Hom.isClopen_range` — an open immersion that is universally
  closed has clopen range.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An open immersion with closed range is a closed immersion. -/
lemma IsClosedImmersion.of_isOpenImmersion [IsOpenImmersion f] (hf : IsClosed (Set.range f)) :
    IsClosedImmersion f :=
  .of_isPreimmersion f hf

/-- An open immersion that is universally closed is a closed immersion. In particular this
applies to a proper open immersion. -/
lemma IsClosedImmersion.of_isOpenImmersion_of_universallyClosed
    [IsOpenImmersion f] [UniversallyClosed f] :
    IsClosedImmersion f :=
  .of_isOpenImmersion f f.isClosedMap.isClosed_range

/-- The range of an open immersion that is universally closed is clopen. -/
lemma Scheme.Hom.isClopen_range [IsOpenImmersion f] [UniversallyClosed f] :
    IsClopen (Set.range f) :=
  ⟨f.isClosedMap.isClosed_range, f.isOpenEmbedding.isOpen_range⟩

end AlgebraicGeometry
