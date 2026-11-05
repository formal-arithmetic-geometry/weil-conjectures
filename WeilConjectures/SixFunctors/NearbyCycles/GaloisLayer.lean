/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GaloisFieldCover
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionComp
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeGenericUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisCoverTrace

/-!

# Finite Galois layers of the generic fibre of a model

Let `N` be a model of `X` with special fibre `X'`, let `h : N.generic ⟶ Spec L` be a morphism to
the spectrum of a field and let `L'/L` be a finite Galois extension with group `Γ`. The
*Galois layer* `N_{L'}` (`NearbyCyclesModel.galoisLayer`) is the model with the total space and
special fibre of `N` and generic fibre `G = N.generic ×_{Spec L} Spec L'`, mapped to `N` by the
projection `g : G ⟶ N.generic` (`NearbyCyclesModel.galoisLayerHom`). The group `Γ` acts on
`N_{L'}` over the identities (`NearbyCyclesModel.galoisLayerAut`), and this action on the nearby
cycles is multiplicative (`NearbyCyclesModel.galoisLayerAut_autAction_mul`). This is the step
"finite layers" of SGA 4½ [Th. finitude] §3.

## Main results

- `NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom`: if multiplication by
  `|Γ|` is invertible on `Lε^* C`, the pullback exchange `α : L(𝟙)^* Ψ_N C ⟶ Ψ_{N_{L'}} L(𝟙)^* C`
  of the projection has a retraction `r`, whose idempotent is the average of the transported
  derived Galois actions: `|Γ| • (r ≫ α) = ∑ σ, κ⁻¹ ≫ Ψ'(ρ_σ) ≫ κ`, for `Ψ' = Li^* Rj_*`, the
  derived action `ρ_σ` of `σ` on `Rg_* Lg^*` and the canonical isomorphism
  `κ : Li^* Rj_* Rg_* Lg^* Lε^* C ≅ Ψ_{N_{L'}} L(𝟙)^* C`
  (`NearbyCyclesModel.galoisLayerExchangeIso`).

The proof computes `α` as `Ψ'` of the unit of `Lg^* ⊣ Rg_*` up to canonical isomorphisms
(`NearbyCyclesModel.Hom.pullbackExchange_app_of_total_eq_id`) and splits that unit by the
normalized derived Galois trace (`ProEtale.CondensedRing.derivedUnit_comp_normalizedTrace`); the
abstract part is `CategoryTheory.exists_retraction_of_eq_comp_map_comp`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (L' : Type u) [Field L'] [Algebra L L']

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable [FiniteDimensional L L'] [IsGalois L L']

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
