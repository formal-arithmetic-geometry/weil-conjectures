/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Morphisms to the spectrum of a field are flat

Every morphism `X ⟶ Spec k` to the spectrum of a field is flat.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Every morphism to the spectrum of a field is flat.** Affine-locally `X ⟶ Spec k` is given
by a ring map `k ⟶ A`, and `A` is a free, hence flat, `k`-module. This is the instance for
morphisms to an integral scheme with a single point.

(blueprint: `lem-pc-flat-field`) -/
theorem Flat.of_field {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Flat f :=
  inferInstance

end AlgebraicGeometry
