/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FieldTheory.GaloisRestriction
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisInvariantsProjector
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisTraitChange
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Change of trait from the change of Galois layers, for torsion coefficients of étale origin

Let `τ : N₂ ⟶ N₁` be a morphism of models over `Spec l : Spec L₂ ⟶ Spec L₁`, `ω : Ω₁ ⟶ Ω₂` a
homomorphism of Galois extensions over `l` such that `L₁` is relatively closed in `L₂` inside
`Ω₂`, and `Λ = C(-, T₀)` for a finite discrete ring `T₀` in which the degrees of the finite Galois
subextensions of `Ωᵢ/Lᵢ` are invertible. For `C` such that `Lεᵢ^*` of `C` (resp. of `Lf^* C`) is
bounded below of étale origin, if the change of Galois layers `α_{τ'}` is invertible, so is the
change of trait `α_τ` (SGA 4½, [Th. finitude], proof of 3.7, 3.8)
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin_generic`).

This combines `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap` with the
projectors onto the Galois invariants
(`NearbyCyclesModel.exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector`)
for the family `σ ↦ (σ|_{Ω₁}, σ)` of `Aut(Ω₂/L₂)`, whose restrictions to every finite Galois
subextension of `Ω₁/L₁` are surjective (`AlgEquiv.exists_restrictNormalHomAlong_eq`).

Compared with
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_galoisLayerMap_of_plusEtaleOrigin`
(`WeilConjectures.SixFunctors.NearbyCycles.GaloisTraitChangeTorsion`), the étale-origin hypotheses
are only asked on the generic fibres, which is the form available in the slice step.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {X₁ X₁' X₂ X₂' : Scheme.{u}} {N₁ : NearbyCyclesModel X₁ X₁'}
  {N₂ : NearbyCyclesModel X₂ X₂'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  {L₁ L₂ : Type u} [Field L₁] [Field L₂] {h₁ : N₁.generic ⟶ Spec (.of L₁)}
  {h₂ : N₂.generic ⟶ Spec (.of L₂)} {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [Algebra L₁ Ω₁]
  [Algebra L₂ Ω₂] {l : L₁ →+* L₂} {ω : Ω₁ →+* Ω₂}
  {hω : ω.comp (algebraMap L₁ Ω₁) = (algebraMap L₂ Ω₂).comp l}

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
