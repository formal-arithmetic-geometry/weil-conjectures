/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Immersions that are universally closed

An immersion identifies its source with a locally closed subscheme of its target. If it is
moreover universally closed — for instance if it is proper — then that locally closed subset
is closed, so the immersion is a closed immersion.

In particular an immersion of a scheme proper over a base `S` into a scheme separated over `S`
is automatically a closed immersion: the immersion is universally closed because the composite
with the separated structure morphism of the target is.

Note that `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` cannot host this result:
`Mathlib.AlgebraicGeometry.Morphisms.Immersion` imports it, so the dependency only runs the
other way.

## Main results

- `AlgebraicGeometry.IsClosedImmersion.of_isImmersion_of_universallyClosed` — a universally
  closed immersion is a closed immersion.
- `AlgebraicGeometry.IsClosedImmersion.of_isImmersion_of_universallyClosed_comp` — an immersion
  whose composite with a separated morphism is universally closed is a closed immersion.
- `AlgebraicGeometry.IsClosedImmersion.of_isImmersion_over` — an immersion of a universally
  closed `S`-scheme, for instance of a proper `S`-scheme, into a separated `S`-scheme is a
  closed immersion.
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

/-- **An immersion whose composite with a separated morphism is universally closed is a closed
immersion**:

```
        f
   X ─────────→ Y
     ╲          │
      ╲ f ≫ g   │ g   (g separated)
       ↘        ↓
                S     (f ≫ g universally closed)
```
-/
lemma IsClosedImmersion.of_isImmersion_of_universallyClosed_comp {S : Scheme.{u}} (g : Y ⟶ S)
    [IsImmersion f] [IsSeparated g] [UniversallyClosed (f ≫ g)] :
    IsClosedImmersion f :=
  -- the immersion is then itself universally closed
  have : UniversallyClosed f := .of_comp_of_isSeparated f g
  .of_isImmersion_of_universallyClosed f

/-- **An immersion of a universally closed `S`-scheme into a separated `S`-scheme is a closed
immersion.**

```
        f
   X ─────────→ Y
     ╲          ╱
X ↘ S ╲        ╱ Y ↘ S
       ↘      ↙
          S
```

In particular this applies to a proper `S`-scheme `X`, and is what makes the notion of a very
ample line bundle on a proper scheme behave: an immersion into a projective space is
automatically a closed immersion. -/
lemma IsClosedImmersion.of_isImmersion_over (S : Scheme.{u}) [X.Over S] [Y.Over S] [f.IsOver S]
    [IsImmersion f] [UniversallyClosed (X ↘ S)] [IsSeparated (Y ↘ S)] :
    IsClosedImmersion f :=
  have : UniversallyClosed (f ≫ Y ↘ S) := by
    rw [comp_over]
    infer_instance
  .of_isImmersion_of_universallyClosed_comp f (Y ↘ S)

end AlgebraicGeometry
