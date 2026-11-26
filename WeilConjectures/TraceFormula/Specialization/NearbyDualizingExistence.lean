/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingOpen

/-!

# Existence of the dualizing maps of nearby cycles

The dualizing maps `θ_N` of the trait models over the base
(`NearbyCyclesModel.IsTraitModelOfBase.dualizingMap`) form a family
`NearbyCyclesModel.NearbyDualizingData` (`NearbyCyclesModel.nonempty_nearbyDualizingData`).

## Implementation details

The hypothesis that the geometric generic fibre `𝒳_Ω` is all of `X ×_k Spec Ω` in the proper
property is necessary: if `𝒳_Ω` is only an open of `X ×_k Spec Ω` (as
`NearbyCyclesModel.IsTraitModelOfBase` allows), `Ψ_M` only sees the part of `X` met by `𝒳_Ω`,
while `tr_X` sees all of `X` (for `X = Spec k ⊔ Spec k` and the trait itself as total space over
the first copy, the left side vanishes on the second summand of `Ra_* ω_X = ℚ̄_ℓ ⊕ ℚ̄_ℓ` and the
right side does not). With it, `χ_a` is the proper base change isomorphism
`RΓ(X_Ω, -) ≅ RΓ(X', Ψ -)`, and the property is the compatibility of `β_a` with traces.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']


/-- **The dualizing maps of nearby cycles over the trait**: the dualizing maps
`θ_M = β_a(ℚ̄_ℓ) : Ψ_M ω_X ⟶ ω_{X'}` of the trait models over the base form a family
`NearbyCyclesModel.NearbyDualizingData`:
* (**proper models**) if `q : 𝒳 ⟶ S` is proper and the geometric generic fibre `𝒳_Ω` is all of
  `X ×_k Spec Ω`, then `tr_{X'} ∘ Ra'_*(θ_M) ∘ χ_a(ω_X) = σ⁻¹ ∘ Ψ_S(tr_X)`;
* (**open restriction**) if `φ : N ⟶ M` is a morphism of trait models over open immersions
  `j : Y ⟶ X` and `j' : Y' ⟶ X'`, whose map of total spaces is an open immersion compatible with
  the structure morphisms and whose square of geometric generic fibres is cartesian, then
  `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)`. -/
theorem nonempty_nearbyDualizingData : Nonempty (NearbyDualizingData k k' ℓ) :=
  ⟨{ θ := fun h ↦ h.dualizingMap ℓ
     pushforwardExchange_comp_map_θ_comp_trace := fun h _ hgen ↦
       h.pushforwardExchange_app_comp_map_dualizingMap_comp_trace ℓ hgen
     map_θ_comp_dualizingComplexUpperStarIso := fun hM hN j _ j' _ φ _ hφ hq hg ↦
       IsTraitModelOfBase.map_dualizingMap_comp_dualizingComplexUpperStarIso ℓ hM hN j j' φ hφ
         hq hg }⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
