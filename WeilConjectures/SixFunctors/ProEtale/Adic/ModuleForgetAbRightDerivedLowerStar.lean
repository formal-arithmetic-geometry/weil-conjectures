/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar

/-!
# Underlying abelian sheaves of derived direct images of sheaves of modules

Let `Λ` be a commutative ring which is flat over `ℤ` (for instance `ULift ℤ_ℓ`) and
`f : X ⟶ Y` a morphism of schemes. Taking underlying abelian sheaves of pro-étale sheaves of
`Λ`-modules commutes with the derived direct images:
```
Hᵠ(Rf_* F[0])_ab ≅ Hᵠ(Rf_* F_ab[0])
```
(`AlgebraicGeometry.ProEtale.sheafComposeForget₂HomologyRightDerivedLowerStarIso`). The point is
that the forgetful functor has the exact left adjoint `A ↦ (Λ ⊗[ℤ] A)^#`, `Λ` being flat over
`ℤ`, so that it preserves injective objects.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Module.Flat ℤ Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

end AlgebraicGeometry.ProEtale
