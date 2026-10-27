/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchange

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

/-- **The compact-support exchange of a proper model is the inverse of the proper exchange**: for
a trait model `N` of a proper `Y` with proper special fibre and a compactification `C`, the
exchange `ν_C` followed by `Ra_! ≅ Ra_*` and the proper exchange `χ_a` is `Ra'_! ≅ Ra'_*`. -/
theorem Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app
    [IsProper (toPoint Y).left] [IsProper (toPoint Y').left] {h : N.IsTraitModelOfBase k q g}
    (C : h.Compactification) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (C.compactSupportExchange ℓ).app K ≫
        (traitSpecialization k k' (ℓ := ℓ)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app K) ≫
        (h.pushforwardExchange ℓ).app K =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y')).hom.app
        ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj K) :=
  sorry

/-- **The dualizing map of a proper model is compatible with the traces**:
`tr_{Y'} ∘ Ra'_*(θ_N) ∘ χ_a(ω_Y) = σ⁻¹ ∘ Ψ_S(tr_Y)`. -/
theorem pushforwardExchange_app_comp_map_dualizingMap_comp_trace [IsProper (toPoint Y).left]
    [IsProper (toPoint Y').left] (h : N.IsTraitModelOfBase k q g) :
    (h.pushforwardExchange ℓ).app (dualizingComplex ℓ Y) ≫
        (boundedConstructibleLowerStar ℓ (toPoint Y')).map (h.dualizingMap ℓ) ≫ trace ℓ Y' =
      (traitSpecialization k k' (ℓ := ℓ)).map (trace ℓ Y) ≫
        inv (traitSpecializationUnit k k' (ℓ := ℓ)) :=
  sorry

/-- **The dualizing maps are compatible with open restriction**: for an open sub-model `N ⊆ M`
over open immersions `j`, `j'`, `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)`. -/
theorem map_dualizingMap_comp_dualizingComplexUpperStarIso {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {qM : M.total ⟶ trait k'}
    {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
    (hM : M.IsTraitModelOfBase k qM gM) (hN : N.IsTraitModelOfBase k q g)
    (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X') [IsOpenImmersion j'.left]
    (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : q = φ.total ≫ qM)
    (hg : g = φ.generic ≫ gM) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map
        (hM.dualizingMap ℓ) ≫ (dualizingComplexUpperStarIso ℓ j').hom =
      (φ.boundedConstructiblePullbackExchange ℓ (hN.preservesBoundedConstructible ℓ)
          (hM.preservesBoundedConstructible ℓ)).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible ℓ)).map
          (dualizingComplexUpperStarIso ℓ j).hom ≫ hN.dualizingMap ℓ :=
  sorry

end IsTraitModelOfBase

variable (k k')

/-- **The dualizing maps of nearby cycles over the trait** (blueprint `det-nearby-exchange-maps`
(4)–(5) and its independence of the compactification, with the composition law
`θ_V = f_s^! θ_W ∘ β_f(ω_W)` of `sk-lem-tf-nearby-mate-coherences` (4); proved there from the
pullback and proper exchanges of `det-sp-nearby-cycles-exchanges` and Nagata's compactification
theorem). The dualizing maps `θ_M = β_a(ℚ̄_ℓ) : Ψ_M ω_X ⟶ ω_{X'}` of the trait models over the base,
read through the specialization unit of the trait and `Lε^* ω_{X/k} ≅ ω_{𝒳_Ω/Ω}`, form a family
`NearbyCyclesModel.NearbyDualizingData`:
* (**proper models**) if `q : 𝒳 ⟶ S` is proper and the geometric generic fibre `𝒳_Ω` is all of
  `X ×_k Spec Ω` (a pullback square), then `ν_a = χ_a⁻¹` (under `Ra_! ≅ Ra_*`) gives
  `tr_{X'} ∘ Ra'_*(θ_M) ∘ χ_a(ω_X) = σ⁻¹ ∘ Ψ_S(tr_X)`;
* (**open restriction**) if `φ : N ⟶ M` is a morphism of trait models over open immersions
  `j : Y ⟶ X` and `j' : Y' ⟶ X'`, whose map of total spaces is an open immersion compatible with
  the structure morphisms and whose square of geometric generic fibres is cartesian, then
  `β_j = α_j⁻¹` and `j^! = j^*` give `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)`.

These properties determine the family (see the module docstring). The hypothesis that `𝒳_Ω` is
all of `X ×_k Spec Ω` in the proper property is necessary: if `𝒳_Ω` is only an open of
`X ×_k Spec Ω` (as `NearbyCyclesModel.IsTraitModelOfBase` allows), `Ψ_M` only sees the part of `X`
met by `𝒳_Ω`, while `tr_X` sees all of `X` (for `X = Spec k ⊔ Spec k` and the trait itself as
total space over the first copy, the left side vanishes on the second summand of
`Ra_* ω_X = ℚ̄_ℓ ⊕ ℚ̄_ℓ` and the right side does not). With it, `χ_a` is the proper base change
isomorphism `RΓ(X_Ω, -) ≅ RΓ(X', Ψ -)`, and the property is the compatibility of `β_a` with
traces. -/
theorem nonempty_nearbyDualizingData : Nonempty (NearbyDualizingData k k' ℓ) :=
  ⟨{ θ := fun h ↦ h.dualizingMap ℓ
     pushforwardExchange_comp_map_θ_comp_trace := fun h _ _ ↦
       h.pushforwardExchange_app_comp_map_dualizingMap_comp_trace ℓ
     map_θ_comp_dualizingComplexUpperStarIso := fun hM hN j _ j' _ φ _ hφ hq hg ↦
       IsTraitModelOfBase.map_dualizingMap_comp_dualizingComplexUpperStarIso ℓ hM hN j j' φ hφ
         hq hg }⟩

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
