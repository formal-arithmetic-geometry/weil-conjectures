/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# `Spec ℤ` is locally Noetherian

The terminal scheme `Spec (ULift ℤ)` is locally Noetherian
(`AlgebraicGeometry.isLocallyNoetherian_spec_uliftInt`), because `ℤ` is a Noetherian ring.
This is what makes a scheme of finite type over `ℤ` Noetherian.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- `Spec ℤ` is a locally Noetherian scheme. -/
instance isLocallyNoetherian_spec_uliftInt :
    IsLocallyNoetherian (Spec <| .of <| ULift.{u} ℤ) :=
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  inferInstance

end AlgebraicGeometry
