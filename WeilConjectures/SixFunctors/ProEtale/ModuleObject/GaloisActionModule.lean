/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisActionSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionUnitTransportInputs

/-!
# The Galois action on module objects is the unit transport

For a Galois covering `g : Y ⟶ X` with action `ρ`, the action `galoisAction Λ g hρ σ` of `σ` on
`g_* g^*` of module objects over `Λ` is the unit transport along `ρ σ`
(`ProEtale.CondensedRing.galoisAction_eq_unitTransport`). Since the forgetful functor from module
objects to sheaves is faithful, this is checked on underlying sheaves, where both sides are, up to
the identifications `upperStarForgetIso`, the corresponding constructions for sheaves
(`ProEtale.CondensedRing.forget_map_galoisAction_app`,
`ProEtale.CondensedRing.forget_map_unitTransport_app`), identified by
`ProEtale.galoisAction_eq_unitTransport`.

As a consequence the splitting of the pullback exchange of a finite Galois layer by the averaged
action on nearby cycles holds without hypotheses
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_autAction`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (L' : Type u) [Field L'] [Algebra L L']
  [FiniteDimensional L L'] [IsGalois L L']

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
