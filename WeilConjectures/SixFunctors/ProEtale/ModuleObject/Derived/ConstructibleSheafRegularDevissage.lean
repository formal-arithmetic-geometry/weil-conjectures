/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GenericFiber.GenericRegularity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafDevissage

/-!
# Dévissage of constructible sheaves to lisse sheaves on connected regular schemes

Variant of `ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject` for a scheme
`T` locally of finite type over a perfect field `k`: the generators `Rc_* j_! Rc'_* L` of the
dévissage may be taken with `c' : E ⟶ V` a surjective closed immersion from a connected regular
noetherian scheme `E`
(`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject_of_perfectField`).

In the induction step the open `V` contained in a stratum is shrunk, by generic smoothness, to a
nonempty open which is, up to a surjective closed immersion, a connected regular scheme
(`AlgebraicGeometry.exists_isRegular_isClosedImmersion_of_perfectField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
