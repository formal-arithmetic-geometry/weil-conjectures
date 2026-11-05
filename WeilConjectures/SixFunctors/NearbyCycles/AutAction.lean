/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethPullback

/-!

# Automorphisms of models acting on nearby cycles

A morphism of models `σ : M ⟶ M` over the identities of `X` and `X'` (for instance an
automorphism of the geometric generic fibre over the generic point of the trait) acts on the
nearby cycles by its pullback exchange, transported along `L(𝟙)^* ≅ 𝟭`
(`NearbyCyclesModel.Hom.autAction`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
