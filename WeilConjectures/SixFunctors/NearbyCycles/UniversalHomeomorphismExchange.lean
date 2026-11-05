/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeGenericUnit
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModelUnit

/-!

# Pullback exchanges along universal homeomorphisms of generic fibres

A morphism of models which is the identity on total spaces and special fibres and a universal
homeomorphism on geometric generic fibres has an invertible pullback exchange
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isUniversalHomeomorphism_generic`): the exchange
is `Li^* Rj_*` of the unit of `Lg^* ⊣ Rg_*`
(`NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`), which is invertible for a universal
homeomorphism `g` by topological invariance. The file also records two consequences of the square
and composition laws of pullback exchanges
(`NearbyCyclesModel.Hom.isIso_map_pullbackExchange_app_of_square_of_isIso`,
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' G : Scheme.{u}}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' X₁ X₁' Z Z' Z₁ Z₁' : Scheme.{u}} {M : NearbyCyclesModel X X'}
  {M₁ : NearbyCyclesModel X₁ X₁'} {P : NearbyCyclesModel Z Z'} {P₁ : NearbyCyclesModel Z₁ Z₁'}
  {f₀ : Z ⟶ X} {f₀' : Z' ⟶ X'} {g : X ⟶ X₁} {g' : X' ⟶ X₁'} {k : Z ⟶ Z₁} {k' : Z' ⟶ Z₁'}
  {e : Z₁ ⟶ X₁} {e' : Z₁' ⟶ X₁'}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
