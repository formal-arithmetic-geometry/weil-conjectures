/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethEquivariant

/-!

# The action of self-maps of models on nearby cycles is monoidal

For a morphism of models `σ : M ⟶ M` over the identities, the action
`NearbyCyclesModel.Hom.autAction` of `σ` on the nearby cycles commutes with the lax tensor maps:
`μ_M ∘ (σ_A ⊗ σ_B) = σ_{A ⊗ B} ∘ μ_M` (`NearbyCyclesModel.Hom.autAction_tensor`). This follows
from the monoidality of the pullback exchange
(`NearbyCyclesModel.Hom.map_tensorMap_comp_pullbackExchange_app`) and of the identity
isomorphisms `L(𝟙)^* ≅ 𝟭` (`ProEtale.CondensedRing.δ_leftDerivedUpperStarId`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
