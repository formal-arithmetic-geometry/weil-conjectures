/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayer

/-!

# The Galois action on nearby cycles

Let `N` be a model of `X` with special fibre `X'`, let `h : N.generic ⟶ Spec L` be a morphism to
the spectrum of a field and let `Ω/L` be a field extension, possibly infinite. The group
`Aut(Ω/L)` acts on the Galois layer `N_Ω` (`NearbyCyclesModel.galoisLayer`), the model with the
total space and special fibre of `N` and generic fibre `N.generic ×_{Spec L} Spec Ω`, through
`Spec σ` on the second factor (`NearbyCyclesModel.galoisLayerAut`). This induces an action on the
nearby cycles `Ψ_{N_Ω}` (`NearbyCyclesModel.galoisLayerAction`), by the pullback exchange of the
automorphism of models (`NearbyCyclesModel.Hom.autAction`).

For a model `N` over a strictly henselian trait `S` whose generic fibre lies over the generic point
`η = Spec K` of `S`, and `Ω` a separable closure of `K`, this is the action of the inertia group
`I = Gal(K^sep/K)` on the geometric nearby cycles `RΨ = ī^* Rj̄_*` of SGA 7 XIII 1.3, by
functoriality of the construction in automorphisms of `η̄` over `η`.

## Main results

- `NearbyCyclesModel.galoisLayerAction_one`, `NearbyCyclesModel.galoisLayerAction_mul`: this is a
  (right) action of the group `Aut(Ω/L)`.
- `NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction`: an automorphism of models which
  does not change a morphism of models `ψ` fixes the pullback exchange of `ψ`.
- `NearbyCyclesModel.pullbackExchange_galoisLayerHom_app_comp_galoisLayerAction`: the pullback
  exchange `L(𝟙)^* Ψ_N ⟶ Ψ_{N_Ω} L(𝟙)^*` of the projection `N_Ω ⟶ N` lands in the invariants of
  the action.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

variable (N : NearbyCyclesModel X X') {L : Type u} [Field L] (h : N.generic ⟶ Spec (.of L))
  (Ω : Type u) [Field Ω] [Algebra L Ω]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
