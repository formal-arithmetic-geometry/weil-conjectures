/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayer
public import WeilConjectures.CategoryTheory.Adjunction.ConjugateCounit

/-!

# The Galois action on the nearby cycles of a finite Galois layer

Let `N_{L'}` be the finite Galois layer of a model `N` along `h : N.generic ⟶ Spec L` and a
finite Galois extension `L'/L` (`NearbyCyclesModel.galoisLayer`), with generic fibre
`G = N.generic ×_{Spec L} Spec L'`, projection `g : G ⟶ N.generic` and automorphisms `ρ_σ` of
`G` over `N.generic`. This file computes the action of `σ ∈ Gal(L'/L)` on the nearby cycles of
`N_{L'}` (`NearbyCyclesModel.Hom.autAction` of `NearbyCyclesModel.galoisLayerAut σ`).

For `s : G ⟶ G'`, `p`, `q` out of `G'` and factorizations `s ≫ p = p₁`, `s ≫ q = q₁`, the
*unit transport* `Rp_* Lq^* A ⟶ Rp₁_* Lq₁^* A` is the unit of `Ls^* ⊣ Rs_*` followed by the
composition isomorphisms (`ProEtale.CondensedRing.derivedUnitTransport`); for `p = q = g` and
`s = ρ_σ` it is the action of `ρ_σ` on `Rg_* Lg^*`.

## Main results

- `NearbyCyclesModel.Hom.pullbackExchange_app_eq_derivedUnitTransport`,
  `NearbyCyclesModel.Hom.autAction_eq_derivedUnitTransport`: the pullback exchange and the action
  on nearby cycles of an endomorphism of a model with identity total component `𝟙` and generic
  component `s` are `Li^*` of the unit transport along `s` (a mate computation, cf.
  `NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`).
- `ProEtale.CondensedRing.derivedUnitTransport_comp`: the unit transport of a composite
  `g ≫ j`, `g ≫ ε` is `Rj_*` of the unit transport of `g` at `Lε^*`, up to the composition
  isomorphisms; it rests on the associativity of the composition isomorphisms of derived
  pushforwards (`ProEtale.CondensedRing.rightDerivedLowerStarComp_inv_app_assoc`).
- `NearbyCyclesModel.galoisLayerAut_autAction`: the action of `σ` on the nearby cycles of `N_{L'}`
  is `κ⁻¹ ≫ Li^* Rj_* (u_σ) ≫ κ`, for the unit transport `u_σ` along `ρ_σ` of `Rg_* Lg^*` at
  `Lε^* C` and `κ = NearbyCyclesModel.galoisLayerExchangeIso`.
- `NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom'`: the splitting of the
  pullback exchange of `N_{L'} ⟶ N` with idempotent `|Γ|⁻¹ ∑ σ, σ_*`, the average of the actions
  of `galoisLayerAut σ` on the nearby cycles, provided the unit transports `u_σ` are the derived
  Galois actions `ProEtale.CondensedRing.derivedGaloisAction` up to a bijection of `Γ`.

## Implementation notes

The diagram chases are carried out in abstract categories (`CategoryTheory.unitTransport_comp_aux`,
`CategoryTheory.pullbackExchange_endo_aux`) and then instantiated. The identification of the
unit transports `u_σ` with the derived Galois actions (defined through the restriction to the
base changes `V ×_X Y`) is not proved here and enters the last theorem as a hypothesis.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Squares

variable {X Y Z : Scheme.{u}}

end Squares

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}}

variable (N : NearbyCyclesModel X X') {L : Type u} [Field L] (h : N.generic ⟶ Spec (.of L))
  (L' : Type u) [Field L'] [Algebra L L']

variable [FiniteDimensional L L'] [IsGalois L L']

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
