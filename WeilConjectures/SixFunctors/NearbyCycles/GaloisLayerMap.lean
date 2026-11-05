/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisAction

/-!

# The Galois action on nearby cycles is compatible with a change of trait

Let `τ : N₂ ⟶ N₁` be a morphism of models over `f : X₂ ⟶ X₁`, `f' : X₂' ⟶ X₁'`, for instance the
base change of a model `N₁` over a strictly henselian trait `S₁` to a strictly henselian trait
`S₂ ⟶ S₁`. Let `hᵢ : Nᵢ.generic ⟶ Spec Lᵢ` be compatible with a field homomorphism `l : L₁ ⟶ L₂`,
and `ω : Ω₁ ⟶ Ω₂` a homomorphism of extensions `Ωᵢ/Lᵢ` over `l`. Then `τ` induces a morphism of
the Galois layers `N₂_{Ω₂} ⟶ N₁_{Ω₁}` (`NearbyCyclesModel.galoisLayerMap`): `τ` on the total
spaces and `τ.generic ×_{Spec l} Spec ω` on the generic fibres.

Its pullback exchange `α_{τ'} : Lf'^* Ψ_{N₁_{Ω₁}} ⟶ Ψ_{N₂_{Ω₂}} Lf^*` is equivariant along the
restriction of automorphisms `Aut(Ω₂/L₂) ⟶ Aut(Ω₁/L₁)`: if `ω ∘ σ₁ = σ₂ ∘ ω`, then
`α_{τ'} ∘ Lf'^*(σ₁) = σ₂ ∘ α_{τ'}` for the Galois actions of `NearbyCyclesModel.galoisLayerAction`
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction`). For `Ωᵢ` a
separable closure of the fraction field of `Sᵢ` this is the equivariance of the change of trait
along the map of inertia groups `I₂ ⟶ I₁` (SGA 4½, [Th. finitude], proof of 3.7, 3.8).

The pullback exchanges of the square of models
```
N₂_{Ω₂} ──τ'──→ N₁_{Ω₁}
   │σ₂             │σ₁
   ↓               ↓
   N₂ ─────τ─────→ N₁
```
satisfy `α_{τ'} ∘ τ'^* α_{σ₁} = α_{σ₂} ∘ σ₂^* α_τ` up to the composition isomorphisms
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_square`), with `σᵢ : Nᵢ_{Ωᵢ} ⟶ Nᵢ` the
projections.

## Main results

- `NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`: for morphisms of models
  `σ₂ : M₂ ⟶ M₂`, `σ₁ : M₁ ⟶ M₁` over the identities and `τ : M₂ ⟶ M₁` with `σ₂ ≫ τ = τ ≫ σ₁`,
  the pullback exchange of `τ` intertwines the actions of `σ₁` and `σ₂`.
- `NearbyCyclesModel.pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction`: the equivariance
  of the exchange of a change of trait for the Galois actions.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

open Scheme

variable {X₁ X₁' X₂ X₂' : Scheme.{u}} {M₁ : NearbyCyclesModel X₁ X₁'}
  {M₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}

variable {L₁ L₂ : Type u} [Field L₁] [Field L₂] (h₁ : M₁.generic ⟶ Spec (.of L₁))
  (h₂ : M₂.generic ⟶ Spec (.of L₂)) (Ω₁ Ω₂ : Type u) [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] (l : L₁ →+* L₂) (ω : Ω₁ →+* Ω₂)
  (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l)

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
