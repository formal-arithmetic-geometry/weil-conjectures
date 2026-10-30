/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Change of trait on the invariant summands of nearby cycles (statement)

This file states, without proof, the equivariance step of Deligne's induction for the change of
strictly henselian trait (SGA 4½, [Th. finitude], proof of 3.7, 3.8): for a morphism of models
`τ : N₂ ⟶ N₁` over `Spec l : Spec L₂ ⟶ Spec L₁` and a homomorphism `ω : Ω₁ ⟶ Ω₂` of extensions,
with change of Galois layers `τ' : N₂_{Ω₂} ⟶ N₁_{Ω₁}` (`NearbyCyclesModel.galoisLayerMap`), if the
exchanges `α_{σᵢ}` of the projections `σᵢ : Nᵢ_{Ωᵢ} ⟶ Nᵢ` are the inclusions of the invariant
summands and `α_{τ'}` is invertible, then `α_τ` is invertible
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap`).

It is proved on the branch `trace2/nearby-trait-equivariance` (item 3 of the 3.7 list of PR #1790),
in a file of the same name; the statement here is copied verbatim from that branch, and the proof
is `sorry`ed here until that branch lands. `NearbyCyclesModel.galoisLayerMap` and the equivariance
of `α_{τ'}` (`WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap`) are byte-identical copies
from that branch.

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
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] {l : L₁ →+* L₂} {ω : Ω₁ →+* Ω₂}
  {hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l}

set_option maxHeartbeats 1600000 in
-- the statement involves several large derived functor objects
/-- **Change of trait on the invariant summands** (SGA 4½, [Th. finitude], proof of 3.7, 3.8). Let
`τ : N₂ ⟶ N₁` be a morphism of models over `Spec l`, `ω : Ω₁ ⟶ Ω₂` a homomorphism of extensions
over `l`, `τ'` the change of Galois layers, and `σᵢ : Nᵢ_{Ωᵢ} ⟶ Nᵢ` the projections. Assume
* the exchanges `α_{σᵢ}` have retractions `rᵢ` (Lemme 3.4: `Ψ_{Nᵢ}` is a direct summand of
  `Ψ_{Nᵢ_{Ωᵢ}}`), the projector `r₂ ≫ α_{σ₂}` being invariant under the Galois action of
  `Aut(Ω₂/L₂)`;
* the projector `r₁ ≫ α_{σ₁}` is the projector onto the invariants of the family `(σ k).1` of
  elements of `Aut(Ω₁/L₁)`: on cohomology sheaves of the pullback to `X₂'`, every map invariant
  under the `(σ k).1` is fixed by it;
* each `(σ k).1` is the restriction of `(σ k).2 ∈ Aut(Ω₂/L₂)` along `ω`.
If the change of Galois layers `α_{τ'}` is invertible, so is the change of trait `α_τ`. -/
theorem Hom.isIso_pullbackExchange_app_of_galoisLayerMap (τ : N₂.Hom N₁ f f')
    (hτ : τ.generic ≫ h₁ = h₂ ≫ Spec.map (CommRingCat.ofHom l))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj Λ X₁)))
    {κ : Type*} (σ : κ → (Ω₁ ≃ₐ[L₁] Ω₁) × (Ω₂ ≃ₐ[L₂] Ω₂))
    (hσ : ∀ k x, ω ((σ k).1 x) = (σ k).2 (ω x))
    (h₁split : ∃ r₁, ((N₁.galoisLayerHom h₁ Ω₁).pullbackExchange Λ).app C ≫ r₁ = 𝟙 _ ∧
      ∀ (q : ℤ) {W : Mod (Sheaf (Scheme.ProEt.topology X₂') Ab.{u + 1})
        (condensedRingObj Λ X₂')}
      (φ : (DerivedCategory.homologyFunctor _ q).obj (L((f')^*⟦Λ⟧).obj
        (((N₁.galoisLayer h₁ Ω₁).nearbyCycles Λ).obj (L((𝟙 X₁)^*⟦Λ⟧).obj C))) ⟶ W),
      (∀ k, (DerivedCategory.homologyFunctor _ q).map (L((f')^*⟦Λ⟧).map
        (N₁.galoisLayerAction Λ h₁ Ω₁ (σ k).1 (L((𝟙 X₁)^*⟦Λ⟧).obj C))) ≫ φ = φ) →
      (DerivedCategory.homologyFunctor _ q).map (L((f')^*⟦Λ⟧).map
        (r₁ ≫ ((N₁.galoisLayerHom h₁ Ω₁).pullbackExchange Λ).app C)) ≫ φ = φ)
    (C₂ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₂) Ab.{u + 1})
      (condensedRingObj Λ X₂))) (hC₂ : L((f)^*⟦Λ⟧).obj C = C₂)
    (h₂split : ∃ r₂, ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app C₂ ≫ r₂ = 𝟙 _ ∧
      ∀ σ₂ : Ω₂ ≃ₐ[L₂] Ω₂, N₂.galoisLayerAction Λ h₂ Ω₂ σ₂ (L((𝟙 X₂)^*⟦Λ⟧).obj C₂) ≫
          (r₂ ≫ ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app C₂) =
        r₂ ≫ ((N₂.galoisLayerHom h₂ Ω₂).pullbackExchange Λ).app C₂)
    [IsIso (((galoisLayerMap Ω₁ Ω₂ ω hω τ hτ).pullbackExchange Λ).app
      (L((𝟙 X₁)^*⟦Λ⟧).obj C))] :
    IsIso ((τ.pullbackExchange Λ).app C) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
