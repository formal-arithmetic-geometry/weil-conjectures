/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchangeRefinement
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange
public import WeilConjectures.TraceFormula.Specialization.TraitModelRefinement
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The compact-support exchange of a trait model over the base

Let `N` be a trait model over the base of a separated `k`-scheme `Y` of finite type, with special
fibre `Y'`, over the strictly henselian trait `S = Spec k'⟦t⟧`. For a compactification `C` of `N`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification`: `N ⊆ P` open in a trait model over the
base with proper total space, over `ι : Y ⟶ X`, `ι' : Y' ⟶ X'`), the compact-support exchange of
the structure morphism `a : Y ⟶ Spec k` (blueprint `det-nearby-exchange-maps` (3)) is
```
ν_C = χ_{a_P}⁻¹ ∘ Ra'_{P*}(ν_ι) : Ra'_! Ψ_N ⟶ Ψ_S Ra_!
```
through `Ra_! ≅ ι_! ⋙ Ra_{P*}`, with `ν_ι` the adjoint of `α_ι⁻¹`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange`, an instance of
`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`).

It does not depend on the compactification: for a refinement `C₃ ⟶ C₁` it is unchanged
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_eq_of_refinement`),
and any two compactifications have a common refinement
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`), so
`ν_{C₁} = ν_{C₂}`
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_eq`).
This is the independence statement of blueprint `det-nearby-exchange-maps`.

## The refinement step

For a refinement `π : P₃ ⟶ P₁` over a proper `p : X₃ ⟶ X₁`, with `ι₁ = ι₃ ≫ p` and `N` cartesian
over `P₁`, the composition law `χ_{a₃} = Ra'_{1*}(χ_π) ∘ χ_{a₁}(Rp_*)` of the proper exchanges and
the identity
```
χ_π(ι₃! K) ∘ Ψ_{P₁}(E_K) ∘ ν_{ι₁}(K) = Rp'_*(ν_{ι₃}(K)) ∘ E'_{Ψ_N K}
```
for the identification `E : ι₁! ≅ Rp_* ι₃!` reduce the claim to the formal
`ProEtale.CondensedRing.compactSupportExchange_comp_eq_aux`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left} {q : N.total ⟶ trait k'}
  {g : N.generic ⟶ Spec (.of (traitGenericField k'))} {h : N.IsTraitModelOfBase k q g}

namespace Compactification

variable (C : h.Compactification)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] in
/-- The proper exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_P` of the structure morphism of a
compactification is invertible on bounded constructible complexes
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient`). -/
lemma isIsoOn_pushforwardExchange :
    IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) C.X.left)).ι
      (C.isTraitModelOfBase.toTrait.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) :=
  fun K ↦ C.isTraitModelOfBase.isIso_pushforwardExchange_app_ambient ℓ C.isPullback_ε _ K.property

instance : IsIso (C.hom.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
  C.hom.isIso_pullbackExchange_of_isOpenImmersion _ C.isPullback_hom_j

/-- **The compact-support exchange of a compactification** (blueprint `det-nearby-exchange-maps`
(3)): for the structure morphisms `a : Y ⟶ Spec k`, `a' : Y' ⟶ Spec k'` and a compactification
`N ⊆ P` over `ι : Y ⟶ X`, `ι' : Y' ⟶ X'`, the exchange `ν = χ_{a_P}⁻¹ ∘ Ra'_{P*}(ν_ι) :
Ra'_! Ψ_N ⟶ Ψ_S Ra_!` (`ProEtale.CondensedRing.compactSupportExchangeOfCompactification`). -/
noncomputable def compactSupportExchange :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ) ⋙
        boundedConstructibleLowerShriek ℓ (toPoint Y') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint Y) ⋙ traitSpecialization k k' (ℓ := ℓ) :=
  compactSupportExchangeOfCompactification ℓ (h.preservesBoundedConstructible ℓ)
    (preservesBoundedConstructible_traitModel ℓ) (comp_toPoint C.ι) (comp_toPoint C.ι') C.hom
    C.isTraitModelOfBase.toTrait (C.isIsoOn_pushforwardExchange ℓ)

/-- **The compact-support exchange is unchanged along a refinement** (blueprint
`det-nearby-exchange-maps`, proof: "compatibility of `ν_h` and `χ_q⁻¹ Rq_{s*}(ν_{h''})`"). -/
theorem compactSupportExchange_eq_of_refinement {C₃ C₁ : h.Compactification}
    (r : C₃.Refinement C₁) : C₃.compactSupportExchange ℓ = C₁.compactSupportExchange ℓ :=
  sorry

/-- **The compact-support exchange does not depend on the compactification** (blueprint
`det-nearby-exchange-maps`): two compactifications have a common refinement
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.exists_refinement`), along which the
compact-support exchange is unchanged
(`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_eq_of_refinement`).
-/
theorem compactSupportExchange_eq (C₁ C₂ : h.Compactification) :
    C₁.compactSupportExchange ℓ = C₂.compactSupportExchange ℓ := by
  obtain ⟨C₃, ⟨r₁⟩, ⟨r₂⟩⟩ := C₁.exists_refinement C₂
  rw [← compactSupportExchange_eq_of_refinement ℓ r₁, compactSupportExchange_eq_of_refinement ℓ r₂]

end Compactification

variable (h) in
/-- The compact-support exchange `ν_a : Ra'_! Ψ_N ⟶ Ψ_S Ra_!` of the structure morphism of a
trait model over the base (blueprint `det-nearby-exchange-maps` (3)): the exchange of any
compactification (`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange`),
which does not depend on it
(`NearbyCyclesModel.IsTraitModelOfBase.compactSupportExchange_eq_compactSupportExchange`). -/
noncomputable def compactSupportExchange :
    boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ) ⋙
        boundedConstructibleLowerShriek ℓ (toPoint Y') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint Y) ⋙ traitSpecialization k k' (ℓ := ℓ) :=
  h.nonempty_compactification.some.compactSupportExchange ℓ

/-- The compact-support exchange of a trait model over the base is that of any of its
compactifications. -/
lemma compactSupportExchange_eq_compactSupportExchange (C : h.Compactification) :
    h.compactSupportExchange ℓ = C.compactSupportExchange ℓ :=
  Compactification.compactSupportExchange_eq ℓ _ _

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase
