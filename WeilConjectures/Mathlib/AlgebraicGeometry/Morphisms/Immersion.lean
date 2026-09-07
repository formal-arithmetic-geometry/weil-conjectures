/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Immersions that are universally closed

An immersion identifies its source with a locally closed subscheme of its target. If it is
moreover universally closed — for instance if it is proper — then that locally closed subset
is closed, so the immersion is a closed immersion.

Note that `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` cannot host this result:
`Mathlib.AlgebraicGeometry.Morphisms.Immersion` imports it, so the dependency only runs the
other way.

## Main results

- `AlgebraicGeometry.IsClosedImmersion.of_isImmersion_of_universallyClosed` — a universally
  closed immersion is a closed immersion.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A proper immersion is a closed immersion**: an immersion that is universally closed has
closed range, hence is a closed immersion. -/
lemma IsClosedImmersion.of_isImmersion_of_universallyClosed [IsImmersion f]
    [UniversallyClosed f] :
    IsClosedImmersion f :=
  .of_isPreimmersion f f.isClosedMap.isClosed_range

end AlgebraicGeometry
