/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# A base change of a morphism locally of finite type has locally noetherian source

## Main statements

- `AlgebraicGeometry.instIsLocallyNoetherianPullback` and its symmetric variant: `X ×ₛ T` is
  locally noetherian as soon as `T` is locally noetherian and `X ⟶ S` is locally of finite type.

Mathlib's `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` is a theorem rather than an
instance, because the morphism cannot be recovered from its source. For a pullback it can, so the
statements below are instances.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X T S : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

instance [LocallyOfFiniteType f] [IsLocallyNoetherian T] : IsLocallyNoetherian (pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)

instance [LocallyOfFiniteType g] [IsLocallyNoetherian X] : IsLocallyNoetherian (pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g)

end AlgebraicGeometry
