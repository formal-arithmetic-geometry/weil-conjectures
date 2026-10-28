/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchangeProper

/-!

# The dualizing maps of nearby cycles over the trait

For a trait model `N` of `Y` over the base, the dualizing map `θ_N : Ψ_N ω_Y ⟶ ω_{Y'}` (blueprint
`det-nearby-exchange-maps` (5)) is the exceptional adjoint of the compact-support exchange
`ν_a : Ra'_! Ψ_N ⟶ Ψ_S Ra_!` of the structure morphism, read through the specialization unit of
the trait (`NearbyCyclesModel.IsTraitModelOfBase.dualizingMap`, an instance of
`ProEtale.CondensedRing.dualizingExchange`). The compact-support exchange is defined through a
compactification and does not depend on it
(`NearbyCyclesModel.IsTraitModelOfBase.compactSupportExchange`).

The two characteristic properties of `NearbyCyclesModel.NearbyDualizingData` hold:

* for a proper model, a compactification is proper over `Y`, and `ν_a = χ_a⁻¹` under `Ra_! ≅ Ra_*`
  (`Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app`),
  so `θ` is compatible with the traces;
* for an open sub-model `N ⊆ M`, a compactification of `M` is one of `N`, along which the
  compact-support exchange of `N` is the composite of the exchange `ν_j = (α_j⁻¹)♯` and that of
  `M`, so the composition law of the dualizing maps
  (`ProEtale.CondensedRing.dualizingExchange_eq_comp`) gives the open restriction property.

Hence `NearbyCyclesModel.nonempty_nearbyDualizingData` (blueprint `det-nearby-exchange-maps`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

namespace IsTraitModelOfBase

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The dualizing map of a trait model over the base** (blueprint `det-nearby-exchange-maps`
(5)): `θ_N = β_a(ℚ̄_ℓ) : Ψ_N ω_Y ⟶ ω_{Y'}`, the exceptional adjoint of the compact-support
exchange `ν_a` (`NearbyCyclesModel.IsTraitModelOfBase.compactSupportExchange`), read through the
specialization unit `σ : ℚ̄_ℓ ≅ Ψ_S ℚ̄_ℓ` of the trait. -/
noncomputable def dualizingMap (h : N.IsTraitModelOfBase k q g) :
    (boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj
      (dualizingComplex ℓ Y) ⟶ dualizingComplex ℓ Y' :=
  dualizingExchange ℓ (traitSpecializationUnit k k' (ℓ := ℓ)) (h.compactSupportExchange ℓ)

/-- **The dualizing map of a proper model is compatible with the traces**:
`tr_{Y'} ∘ Ra'_*(θ_N) ∘ χ_a(ω_Y) = σ⁻¹ ∘ Ψ_S(tr_Y)`, for `q` proper and geometric generic fibre
all of `Y ×_k Spec Ω` (then `χ_a` is invertible, and `ν_a = χ_a⁻¹` under `Ra_! ≅ Ra_*`). -/
theorem pushforwardExchange_app_comp_map_dualizingMap_comp_trace [IsProper (toPoint Y).left]
    [IsProper (toPoint Y').left] (h : N.IsTraitModelOfBase k q g) [IsProper q]
    (hgen : IsPullback N.ε g Y.hom (traitGenericPoint k' ≫ traitToBase k k')) :
    (h.pushforwardExchange ℓ).app (dualizingComplex ℓ Y) ≫
        (boundedConstructibleLowerStar ℓ (toPoint Y')).map (h.dualizingMap ℓ) ≫ trace ℓ Y' =
      (traitSpecialization k k' (ℓ := ℓ)).map (trace ℓ Y) ≫
        inv (traitSpecializationUnit k k' (ℓ := ℓ)) :=
  sorry

end IsTraitModelOfBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
