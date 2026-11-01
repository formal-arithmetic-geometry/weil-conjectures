/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs
public import WeilConjectures.TraceFormula.Specialization.GenericSliceExchangeTransport
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseExtension
public import WeilConjectures.Tactic.TransportExact
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariantsProof

/-!

# The slice exchange as an averaging summand

The pullback exchange `α : p^* Ψ_M ⟶ Ψ_{M''} c^*` of the projection from the generic slice model is,
at a finite level, the inclusion of the summand cut out by the averaging idempotent of a finite
group of Galois automorphisms of the slice model
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_averaging_genericSliceExchange`). This is
the generic-slicing identification `g_s^* Ψ_M ≃ (Ψ_{M''} c^*)^P` of SGA 4½, [Th. finitude], §3
(Lemme 3.4 and 3.7), with the pro-`p` averaging.

It is deduced from the same statement for the base change `M ×_{𝔸¹_S} Spec K⟦t⟧` of `M` along
the generic slice (`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`),
whose exchange agrees with the slice exchange up to isomorphisms intertwining the actions of the
generic automorphisms
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_pullbackExchange_genericSliceHom`). The
restrictions of complexes on `X₁` to the geometric generic fibre extend to the total space
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_boundedConstructible_extension`), as that
statement requires. The finite group is the quotient of the generic automorphisms by the normal
core of the subgroups acting trivially on the two complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed


open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

namespace IsTraitModelOfGenericBase

set_option maxHeartbeats 25600000 in
-- the statement involves the actions of the finite quotient on the slice
/-- **The slice exchange is an averaging summand at a finite level** (blueprint
`det-tf-nearby-duality-slice`, the generic-slicing identification `g_s^* Ψ_M ≃ (Ψ_{M''} c^*)^P`,
with `det-tf-invariants-duality`; SGA 4½, [Th. finitude], §3). For two bounded constructible
complexes `A₁`, `A₂` on `X₁`, the pro-`p` kernel `P` of the map of inertia groups acts on
`Ψ_{M''} c^* A₁` and `Ψ_{M''} c^* A₂` through a finite quotient `Γ`: there are automorphisms
`ψ a` of the generic slice model, the identity on the total space, which act on the geometric
generic point `Spec Ω_K` through automorphisms `σ` over the generic point `η_K` of `Spec K⟦t⟧`
(the elements of `P` act through `Gal(Ω_K/η_K)`), lifting the elements `a ∈ Γ`, such that
`α_{Aᵢ}` is split by `rᵢ`
with `|Γ| • (rᵢ ≫ α_{Aᵢ}) = ∑ₐ ρ(ψ a)` and `ρ(ψ a⁻¹)` inverse to `ρ(ψ a)` on `Ψ_{M''} c^* Aᵢ`.
The order of `Γ` is invertible, the coefficients being `ℚ̄_ℓ`.

`Γ` is the quotient of the generic automorphisms by the normal core of the intersection of the
subgroups of finite index of
`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice` for `A₁` and `A₂`,
transported to the generic slice model by
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_retraction_pullbackExchange_genericSliceHom`,
and `ψ a` is the action `NearbyCyclesModel.genericSliceAut` of a representative of `a`. -/
theorem exists_averaging_genericSliceExchange
    (A₁ A₂ : Dᵇc(X₁.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ (Γ : Type u) (_ : Group Γ) (_ : Fintype Γ)
      (ψ : Γ → (genericSliceModel (traitSliceCoord k') hb).Hom
        (genericSliceModel (traitSliceCoord k') hb) (𝟙 _) (𝟙 _)),
      (∀ a, (ψ a).total = 𝟙 _ ∧ IsIso (ψ a).generic ∧
        ∃ σ : Spec (.of (traitGenericField (traitSliceField k'))) ⟶
            Spec (.of (traitGenericField (traitSliceField k'))),
          σ ≫ traitGenericPointToSpec (traitSliceField k') =
              traitGenericPointToSpec (traitSliceField k') ∧
            (ψ a).generic ≫ pullback.snd _ _ = pullback.snd _ _ ≫ σ) ∧
      (∀ T : Dᵇc((baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left)⟦
        Profinite.padicAlgClRingObj ℓ⟧, IsIso (Fintype.card Γ • 𝟙 T)) ∧
      ∀ A, (A = A₁ ∨ A = A₂) →
        ∃ r : (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj
            ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) ⟶
          (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj
            ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible (ℓ := ℓ))).obj A),
          (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A ≫ r = 𝟙 _ ∧
          Fintype.card Γ • (r ≫ (genericSliceExchange (traitSliceCoord k') ℓ h hb).app A) =
            ∑ a, (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a)).app _ ∧
          ∀ a, (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a⁻¹)).app
              ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) ≫
            (genericSliceSelfAction (traitSliceCoord k') ℓ h hb (ψ a)).app
              ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj A) = 𝟙 _ := by
  classical
  -- the generic-slicing identification for the base change, at `A₁` and `A₂`
  obtain ⟨B₁, hB₁, ⟨eB₁⟩⟩ := h.exists_boundedConstructible_extension A₁.2
  obtain ⟨B₂, hB₂, ⟨eB₂⟩⟩ := h.exists_boundedConstructible_extension A₂.2
  obtain ⟨V₁, _, htriv₁, r₁, hr₁, havg₁⟩ :=
    exists_subgroup_pullbackExchange_baseChangeHom_traitSlice h.isTraitModelOver hb
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A₁.obj A₁.2) hB₁ eB₁
  obtain ⟨V₂, _, htriv₂, r₂, hr₂, havg₂⟩ :=
    exists_subgroup_pullbackExchange_baseChangeHom_traitSlice h.isTraitModelOver hb
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A₂.obj A₂.2) hB₂ eB₂
  -- transported to the generic slice model
  obtain ⟨hinv₁, hsplit₁⟩ := h.exists_retraction_pullbackExchange_genericSliceHom
    (traitSliceCoord k') hb (Profinite.padicAlgClRingObj ℓ) A₁.obj htriv₁ r₁
    (by transport_exact hr₁) (by transport_exact havg₁)
  obtain ⟨hinv₂, hsplit₂⟩ := h.exists_retraction_pullbackExchange_genericSliceHom
    (traitSliceCoord k') hb (Profinite.padicAlgClRingObj ℓ) A₂.obj htriv₂ r₂
    (by transport_exact hr₂) (by transport_exact havg₂)
  -- the finite quotient
  have : V₁.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : V₂.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN⟩ : ∃ N : Subgroup (GenericAut k' (traitSliceField k')),
      N = (V₁ ⊓ V₂).normalCore := ⟨_, rfl⟩
  have : N.Normal := hN ▸ inferInstance
  have : N.FiniteIndex := hN ▸ inferInstance
  have hN₁ : N ≤ V₁ := hN ▸ (Subgroup.normalCore_le _).trans inf_le_left
  have hN₂ : N ≤ V₂ := hN ▸ (Subgroup.normalCore_le _).trans inf_le_right
  have : Fintype (GenericAut k' (traitSliceField k') ⧸ N) := Subgroup.fintypeQuotientOfFiniteIndex
  have hmem : ∀ a : GenericAut k' (traitSliceField k') ⧸ N, a.out * a⁻¹.out ∈ N := fun a ↦ by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.out_eq',
      QuotientGroup.out_eq', mul_inv_cancel]
  obtain ⟨r₁', h₁₁, h₁₂⟩ := hsplit₁ N hN₁
  obtain ⟨r₂', h₂₁, h₂₂⟩ := hsplit₂ N hN₂
  have hex : genericSliceExchange (traitSliceCoord k') ℓ h hb = liftExchange
      ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange
        (Profinite.padicAlgClRingObj ℓ)) _ _ _ _ := rfl
  refine ⟨GenericAut k' (traitSliceField k') ⧸ N, inferInstance, inferInstance,
    fun a ↦ genericSliceAut (traitSliceCoord k') hb a.out,
    fun a ↦ ⟨rfl, ?_, a.out.τ, a.out.τ_comp_traitGenericPointToSpec,
      genericSliceAut_generic_snd _ _ _⟩, fun T ↦ ?_, ?_⟩
  · refine ⟨(genericSliceAut (traitSliceCoord k') hb a.out⁻¹).generic, ?_, ?_⟩ <;>
      apply pullback.hom_ext <;> simp
  · have := isIso_nsmul_id_derived_padicAlgClRingObj ℓ _
      (Fintype.card_ne_zero (α := GenericAut k' (traitSliceField k') ⧸ N)) T.obj
    have : IsIso ((ObjectProperty.ι _).map (Fintype.card
        (GenericAut k' (traitSliceField k') ⧸ N) • 𝟙 T)) := by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
      exact this
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  · rintro A (rfl | rfl)
    · refine ⟨ObjectProperty.homMk r₁', ?_, ?_, fun a ↦ ?_⟩
      · apply ObjectProperty.hom_ext
        rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          ObjectProperty.FullSubcategory.id_hom, hex, liftExchange_app_hom]
        transport_exact h₁₁
      · apply (ObjectProperty.ι _).map_injective
        rw [Functor.map_nsmul, Functor.map_sum, Functor.map_comp, ObjectProperty.ι_map,
          ObjectProperty.ι_map, ObjectProperty.homMk_hom, hex, liftExchange_app_hom]
        transport_exact h₁₂
      · apply ObjectProperty.hom_ext
        rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
          genericSliceSelfAction_app, genericSliceSelfAction_app, ObjectProperty.homMk_hom,
          ObjectProperty.homMk_hom]
        transport_exact (hinv₁ a.out a⁻¹.out (hN₁ (hmem a)))
    · refine ⟨ObjectProperty.homMk r₂', ?_, ?_, fun a ↦ ?_⟩
      · apply ObjectProperty.hom_ext
        rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          ObjectProperty.FullSubcategory.id_hom, hex, liftExchange_app_hom]
        transport_exact h₂₁
      · apply (ObjectProperty.ι _).map_injective
        rw [Functor.map_nsmul, Functor.map_sum, Functor.map_comp, ObjectProperty.ι_map,
          ObjectProperty.ι_map, ObjectProperty.homMk_hom, hex, liftExchange_app_hom]
        transport_exact h₂₂
      · apply ObjectProperty.hom_ext
        rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
          genericSliceSelfAction_app, genericSliceSelfAction_app, ObjectProperty.homMk_hom,
          ObjectProperty.homMk_hom]
        transport_exact (hinv₂ a.out a⁻¹.out (hN₂ (hmem a)))

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
