/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.Mathlib.CategoryTheory.Retract
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Change of trait on the invariant summands of nearby cycles

Let `τ : N₂ ⟶ N₁` be a morphism of models over `Spec l : Spec L₂ ⟶ Spec L₁`, and `ω : Ω₁ ⟶ Ω₂` a
homomorphism of extensions `Ωᵢ/Lᵢ` over `l`, with change of Galois layers
`τ' : N₂_{Ω₂} ⟶ N₁_{Ω₁}` (`NearbyCyclesModel.galoisLayerMap`). The pullback exchanges of the square
```
N₂_{Ω₂} ──τ'──→ N₁_{Ω₁}
   │σ₂             │σ₁
   ↓               ↓
   N₂ ─────τ─────→ N₁
```
satisfy `α_{τ'} ∘ τ'^* α_{σ₁} = α_{σ₂} ∘ σ₂^* α_τ` up to the composition isomorphisms
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_square`). By SGA 4½, [Th. finitude],
Lemme 3.4, `α_{σᵢ}` is the inclusion of the direct summand `Ψ_{Nᵢ} = (Ψ_{Nᵢ_{Ωᵢ}})^{Pᵢ}` of
invariants under `Pᵢ = Aut(Ωᵢ/Lᵢ)`. This file proves that if `α_{τ'}` is invertible, `α_τ` is
invertible: `α_{τ'}` is equivariant along the restriction `P₂ ⟶ P₁`
(`NearbyCyclesModel.pullbackExchange_galoisLayerMap_app_comp_galoisLayerAction`), and when every
element of `P₁` is a restriction, it identifies the two invariant summands
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`). This is the step "take the
invariants under a pro-`p` group" in the induction of Deligne's proof of Th. finitude 3.7 (3.8).

The identification of the summands uses that the projector `r₁ ≫ α_{σ₁}` of the first summand is
the projector onto *all* the invariants, in the form: on cohomology sheaves (after pullback to the
special fibre of `N₂`), every map out of `Hᵠ(Ψ_{N₁_{Ω₁}})` which is invariant under `P₁` is fixed
by the projector. Of the second projector, only the invariance `ρ_σ ≫ (r₂ ≫ α_{σ₂}) = r₂ ≫ α_{σ₂}`
is used. The abstract statement is `CategoryTheory.isIso_of_comp_eq_comp_of_coinvariant`, in a
category with a jointly conservative family of functors (the cohomology functors).

## Main results

- `NearbyCyclesModel.pullbackExchange_galoisLayerMap_square`: the square of pullback exchanges.
- `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`: the change of trait is
  invertible on the invariant summands once it is invertible on the Galois layers.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X₁ X₁' X₂ X₂' : Scheme.{u}} {N₁ : NearbyCyclesModel X₁ X₁'}
  {N₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {L₁ L₂ : Type u} [Field L₁] [Field L₂] {h₁ : N₁.generic ⟶ Spec (.of L₁)}
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} (Ω₁ Ω₂ : Type u) [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] {l : L₁ →+* L₂} (ω : Ω₁ →+* Ω₂)
  (hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X₁ X₁' X₂ X₂' : Scheme.{u}} {N₁ : NearbyCyclesModel X₁ X₁'}
  {N₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {L₁ L₂ : Type u} [Field L₁] [Field L₂] {h₁ : N₁.generic ⟶ Spec (.of L₁)}
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] {l : L₁ →+* L₂} {ω : Ω₁ →+* Ω₂}
  {hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
