/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids

/-! # Underlying curve over the specified stable-moduli fibre base

Source: Stacks Project, Tags 003T and 0E7A
(blueprint: def-sfb-stable-fiber-curve).

The equality in an actual functor fibre transports the family's projection to its
specified base. This construction retains the total curve and makes no choices.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.StablePointedModuli

/-- The underlying curve, transported along the base equality in the actual fibre.
Source: Stacks Project, Tags 003T and 0E7A
(blueprint: def-sfb-stable-fiber-curve). -/
def fiberCurve {S : Scheme.{u}} {g r : ℕ} {T : Over S}
    (C : Fiber S g r T) : Over T.left :=
  Over.mk (C.of.val.projection ≫ (eqToHom C.of.property).left)

end AlgebraicGeometry.StablePointedModuli
