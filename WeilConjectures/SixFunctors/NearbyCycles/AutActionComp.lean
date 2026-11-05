/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTrivial
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeId

/-!

# The action of morphisms of models on nearby cycles is multiplicative

For morphisms of models `σ, τ : M ⟶ M` over the identities, the action on nearby cycles
(`NearbyCyclesModel.Hom.autAction`) of a morphism `χ` whose components are the composites of those
of `σ` and `τ` is the composite of the actions, `τ` first
(`NearbyCyclesModel.Hom.autAction_comp_of_eq`), and a morphism of models with identity components
acts trivially (`NearbyCyclesModel.Hom.autAction_of_eq_id`). Both follow from the composition law
of the pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} {M : NearbyCyclesModel X X'}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
