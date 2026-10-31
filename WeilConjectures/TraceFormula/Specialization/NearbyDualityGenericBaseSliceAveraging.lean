/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GaloisLayerStabilizationAssembly
public import WeilConjectures.TraceFormula.Specialization.GenericSliceModelAut
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariants

/-!

# The slice exchange as an averaging summand

The pullback exchange `α : p^* Ψ_M ⟶ Ψ_{M''} c^*` of the projection from the generic slice model is,
at a finite level, the inclusion of the summand cut out by the averaging idempotent of a finite
group of Galois automorphisms of the slice model
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_averaging_genericSliceExchange`). This is
the generic-slicing identification `g_s^* Ψ_M ≃ (Ψ_{M''} c^*)^P` of SGA 4½, [Th. finitude], §3
(Lemme 3.4 and 3.7), with the pro-`p` averaging.

It is deduced from the same statement for the base change `M_b` of `M` along the slice
(`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`): the generic slice
model `M''` and `M_b` have the same total space and geometric generic fibre, and the projection
`M'' ⟶ M` is the composite of the morphism `κ : M'' ⟶ M_b` with identity components
(`NearbyCyclesModel.genericSliceToBaseChange`, whose exchange is invertible and intertwines the
actions of the generic automorphisms) and of the projection `M_b ⟶ M`.

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

/-- **Transport of an averaging splitting along a factorization**, for abstract categories: let
`a : P₀ ⟶ Z` be identified with `L₀ β` (`L₀ ≅ 𝟭`) through isomorphisms `c₁`, `k`, `e`. If `β` is
split by `rβ` with `n • (rβ ≫ β) = ∑ f i`, and the endomorphisms `f i` correspond under `k` and
`e` to endomorphisms `g i` of `Z`, then `a` is split with `n` times its idempotent `∑ g i`. -/
lemma exists_retraction_of_averaging_conj {E : Type*} [Category E] [Preadditive E] {L₀ : E ⥤ E}
    (I : L₀ ≅ 𝟭 E) {P₀ W Z Z' : E} (a : P₀ ⟶ Z) (β : P₀ ⟶ W) (rβ : W ⟶ P₀)
    (hβ : β ≫ rβ = 𝟙 _) {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → (W ⟶ W))
    (havg : n • (rβ ≫ β) = ∑ i ∈ s, f i) (c₁ : P₀ ⟶ L₀.obj P₀) [IsIso c₁]
    (k : L₀.obj W ⟶ Z') [IsIso k] (e : Z ⟶ Z') [IsIso e] (hx : a ≫ e = c₁ ≫ L₀.map β ≫ k)
    (g : ι → (Z ⟶ Z)) (g' : ι → (Z' ⟶ Z')) (hk : ∀ i, k ≫ g' i = L₀.map (f i) ≫ k)
    (he : ∀ i, g i ≫ e = e ≫ g' i) :
    ∃ r, a ≫ r = 𝟙 _ ∧ n • (r ≫ a) = ∑ i ∈ s, g i := by
  have ha : a = c₁ ≫ L₀.map β ≫ k ≫ inv e := by
    rw [← reassoc_of% hx, IsIso.hom_inv_id, Category.comp_id]
  have hL : ∀ {U V : E} (h : U ⟶ V), L₀.map h = I.hom.app U ≫ h ≫ I.inv.app V := fun h ↦ by
    rw [← I.hom.naturality_assoc, Functor.id_map, Iso.hom_inv_id_app, Category.comp_id]
  refine ⟨e ≫ inv k ≫ L₀.map rβ ≫ inv c₁, ?_, ?_⟩
  · rw [ha]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]
    rw [← L₀.map_comp_assoc, hβ, L₀.map_id, Category.id_comp, IsIso.hom_inv_id]
  · have hr : (e ≫ inv k ≫ L₀.map rβ ≫ inv c₁) ≫ a =
        (e ≫ inv k ≫ I.hom.app W) ≫ (rβ ≫ β) ≫ (I.inv.app W ≫ k ≫ inv e) := by
      rw [ha]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← L₀.map_comp_assoc, hL]
      simp only [Category.assoc]
    rw [hr, Preadditive.comp_nsmul, Preadditive.nsmul_comp, havg, Preadditive.sum_comp,
      Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : (e ≫ inv k ≫ I.hom.app W) ≫ f i ≫ I.inv.app W ≫ k ≫ inv e =
        e ≫ inv k ≫ L₀.map (f i) ≫ k ≫ inv e := by
      rw [hL]
      simp only [Category.assoc]
    rw [hi, ← reassoc_of% (hk i), IsIso.inv_hom_id_assoc, ← reassoc_of% (he i),
      IsIso.hom_inv_id, Category.comp_id]

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

namespace IsTraitModelOfGenericBase

section Ambient

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-- The morphism `κ : M'' ⟶ M_b` from the generic slice model to the base change of `M` along the
slice, over the map of bases `c : X₂ ⟶ X₁` of the generic slice. -/
noncomputable abbrev genericSliceToBaseChangeHom :=
  genericSliceToBaseChange (traitSliceCoord k') h.isTraitModelOver hb
    (h.genericSliceModel_ε_comp_genericSliceBaseMap (traitSliceCoord k') hb)

/-- The projection `M'' ⟶ M` from the generic slice model is the composite of
`κ : M'' ⟶ M_b` and of the projection `M_b ⟶ M` from the base change: composition law of the
pullback exchanges. -/
lemma genericSliceHom_pullbackExchange_app_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj Λ X₁.left))) :
    ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange Λ).app A ≫
        ((genericSliceModel (traitSliceCoord k') hb).nearbyCycles Λ).map
          ((leftDerivedUpperStarCompOfEq Λ
            (Category.comp_id (h.genericSliceBaseMap (traitSliceCoord k') hb))).hom.app A) =
      (leftDerivedUpperStarCompOfEq Λ
          (Category.id_comp (sliceSpecialMap (traitSliceCoord k') h.isTraitModelOver hb))).hom.app
          ((M.nearbyCycles Λ).obj A) ≫
        L((𝟙 _)^*⟦Λ⟧).map (((baseChangeHom h.isTraitModelOver b hb
          (traitSlice (traitSliceCoord k')) (traitSlice_over _)).pullbackExchange Λ).app A) ≫
        ((genericSliceToBaseChangeHom h hb).pullbackExchange Λ).app
          (L((𝟙 X₁.left)^*⟦Λ⟧).obj A) :=
  (genericSliceToBaseChangeHom h hb).pullbackExchange_comp_app_of_eq Λ
    (baseChangeHom h.isTraitModelOver b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _))
    (h.genericSliceHom (traitSliceCoord k') hb) (Category.comp_id _) (Category.id_comp _)
    (Category.id_comp _) (Category.id_comp _) A

/-- **The slice exchange is an averaging summand** (ambient derived categories): for a bounded
constructible `A` on `X₁`, there is a subgroup `V` of finite index of the pro-`p` kernel `P'`
acting trivially on `Ψ_{M''} (c^* A)`, and for every subgroup `U ≤ V` of finite index, the
pullback exchange `α : p^* Ψ_M A ⟶ Ψ_{M''} (c^* A)` of the projection from the generic slice
model is split, with `[P' : U]` times its idempotent the sum of the actions of representatives of
`P' ⧸ U`. Deduced from the same statement for the base change `M_b`
(`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice`) through the
morphism `κ : M'' ⟶ M_b` with identity components. -/
theorem exists_subgroup_genericSliceHom_pullbackExchange
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X₁.left)))
    (hA : boundedConstructible _ A) :
    ∃ V : Subgroup (GenericAut k' (traitSliceField k')), V.FiniteIndex ∧
      (∀ σ ∈ V, (genericSliceAut (traitSliceCoord k') hb σ).autAction
          (Profinite.padicAlgClRingObj ℓ)
          (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            A) = 𝟙 _) ∧
      ∀ U : Subgroup (GenericAut k' (traitSliceField k')), U ≤ V →
        ∀ _ : Fintype (GenericAut k' (traitSliceField k') ⧸ U),
        ∃ r, ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A ≫ r = 𝟙 _ ∧
          Fintype.card (GenericAut k' (traitSliceField k') ⧸ U) •
              (r ≫ ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange
                (Profinite.padicAlgClRingObj ℓ)).app A) =
            ∑ σ : GenericAut k' (traitSliceField k') ⧸ U,
              (genericSliceAut (traitSliceCoord k') hb σ.out).autAction
                (Profinite.padicAlgClRingObj ℓ)
                (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦
                  Profinite.padicAlgClRingObj ℓ⟧).obj A) := by
  obtain ⟨V, hV, htriv, rB, hrB, havgB⟩ :=
    exists_subgroup_pullbackExchange_baseChangeHom_traitSlice (ℓ := ℓ) h.isTraitModelOver hb
      (A := A) (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A hA)
  have hκ := fun σ ↦ pullbackExchange_genericSliceToBaseChange_app_comp_autAction
    (traitSliceCoord k') h.isTraitModelOver hb
    (h.genericSliceModel_ε_comp_genericSliceBaseMap (traitSliceCoord k') hb)
    (Profinite.padicAlgClRingObj ℓ) σ (L((𝟙 X₁.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)
  -- triviality of the action of `V` on `Ψ_{M''} (c^* A)`
  have htrivG : ∀ σ ∈ V, (genericSliceAut (traitSliceCoord k') hb σ).autAction
      (Profinite.padicAlgClRingObj ℓ)
      (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        A) = 𝟙 _ := by
    intro σ hσ
    refine eq_id_of_naturality_of_iso _
      (fun f ↦ Hom.autAction_naturality _ _ f)
      ((leftDerivedUpperStarCompOfEq (Profinite.padicAlgClRingObj ℓ)
        (Category.comp_id (h.genericSliceBaseMap (traitSliceCoord k') hb))).app A) ?_
    have h₁ := hκ σ
    rw [htriv σ hσ, CategoryTheory.Functor.map_id, Category.id_comp] at h₁
    exact (cancel_epi _).1 (h₁.trans (Category.comp_id _).symm)
  refine ⟨V, Subgroup.finiteIndex_of_finite_quotient, htrivG, fun U hUV _ ↦ ?_⟩
  have havgU : Fintype.card (GenericAut k' (traitSliceField k') ⧸ U) •
      (rB ≫ ((baseChangeHom h.isTraitModelOver b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over _)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A) =
      ∑ σ : GenericAut k' (traitSliceField k') ⧸ U,
        (baseChangeAut h.isTraitModelOver b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over _) σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
            (L((𝟙 X₁.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) := by
    rw [sum_autAction_baseChangeAut_eq_relIndex_nsmul _ _ _ _ _ _ hUV _ htriv, ← havgB,
      smul_smul, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Subgroup.index, ← Subgroup.index, Subgroup.relIndex_mul_index hUV]
  exact exists_retraction_of_averaging_conj
    (leftDerivedUpperStarId (Profinite.padicAlgClRingObj ℓ) _) _ _ rB hrB Finset.univ _ _ havgU
    _ _ _ (genericSliceHom_pullbackExchange_app_comp h hb _ A)
    (fun σ : GenericAut k' (traitSliceField k') ⧸ U ↦
      (genericSliceAut (traitSliceCoord k') hb σ.out).autAction (Profinite.padicAlgClRingObj ℓ)
        (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          A))
    (fun σ ↦ (genericSliceAut (traitSliceCoord k') hb σ.out).autAction
      (Profinite.padicAlgClRingObj ℓ)
        (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
          (L((𝟙 X₁.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)))
    (fun σ ↦ hκ σ.out) (fun σ ↦ Hom.autAction_naturality _ _ _)

end Ambient

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
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

`Γ` is the quotient of the group of generic automorphisms by the normal core of the intersection
of the subgroups `Vᵢ` of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_subgroup_genericSliceHom_pullbackExchange`
for `A₁` and `A₂`, and `ψ a` the action (`NearbyCyclesModel.genericSliceAut`) of a
representative of `a`. -/
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
  obtain ⟨V₁, hV₁, htriv₁, havg₁⟩ :=
    exists_subgroup_genericSliceHom_pullbackExchange ℓ h hb A₁.obj A₁.property
  obtain ⟨V₂, hV₂, htriv₂, havg₂⟩ :=
    exists_subgroup_genericSliceHom_pullbackExchange ℓ h hb A₂.obj A₂.property
  let N := (V₁ ⊓ V₂).normalCore
  let _ : Fintype (GenericAut k' (traitSliceField k') ⧸ N) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  have hN₁ : N ≤ V₁ := (Subgroup.normalCore_le _).trans inf_le_left
  have hN₂ : N ≤ V₂ := (Subgroup.normalCore_le _).trans inf_le_right
  refine ⟨GenericAut k' (traitSliceField k') ⧸ N, inferInstance, inferInstance,
    fun a ↦ genericSliceAut (traitSliceCoord k') hb a.out, fun a ↦ ⟨rfl, inferInstance, a.out.τ,
      a.out.τ_comp_traitGenericPointToSpec, genericSliceAut_generic_snd _ _ _⟩, fun T ↦ ?_, ?_⟩
  · have : IsIso ((ObjectProperty.ι _).map
        (Fintype.card (GenericAut k' (traitSliceField k') ⧸ N) • 𝟙 T)) := by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
      exact isIso_nsmul_id_derived_padicAlgClRingObj ℓ _ Fintype.card_ne_zero _
    exact isIso_of_reflects_iso _ (ObjectProperty.ι _)
  rintro A hA
  obtain ⟨V, htriv, havg, hNV⟩ : ∃ V : Subgroup (GenericAut k' (traitSliceField k')),
      (∀ σ ∈ V, (genericSliceAut (traitSliceCoord k') hb σ).autAction
          (Profinite.padicAlgClRingObj ℓ)
          (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            A.obj) = 𝟙 _) ∧
      (∀ U : Subgroup (GenericAut k' (traitSliceField k')), U ≤ V →
        ∀ _ : Fintype (GenericAut k' (traitSliceField k') ⧸ U),
        ∃ r, ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A.obj ≫ r = 𝟙 _ ∧
          Fintype.card (GenericAut k' (traitSliceField k') ⧸ U) •
              (r ≫ ((h.genericSliceHom (traitSliceCoord k') hb).pullbackExchange
                (Profinite.padicAlgClRingObj ℓ)).app A.obj) =
            ∑ σ : GenericAut k' (traitSliceField k') ⧸ U,
              (genericSliceAut (traitSliceCoord k') hb σ.out).autAction
                (Profinite.padicAlgClRingObj ℓ)
                (L((h.genericSliceBaseMap (traitSliceCoord k') hb)^*⟦
                  Profinite.padicAlgClRingObj ℓ⟧).obj A.obj)) ∧ N ≤ V := by
    rcases hA with rfl | rfl
    · exact ⟨V₁, htriv₁, havg₁, hN₁⟩
    · exact ⟨V₂, htriv₂, havg₂, hN₂⟩
  obtain ⟨r, hr, hravg⟩ := havg N hNV inferInstance
  refine ⟨ObjectProperty.homMk r, ObjectProperty.hom_ext _ hr, ?_, fun a ↦ ?_⟩
  · apply (ObjectProperty.ι _).map_injective
    rw [Functor.map_nsmul, Functor.map_sum]
    exact hravg
  · apply ObjectProperty.hom_ext
    refine ((autAction_genericSliceAut_mul (traitSliceCoord k') hb _ a.out (a⁻¹).out _).symm).trans
      (htriv _ (hNV ?_))
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.out_eq',
      QuotientGroup.out_eq', mul_inv_cancel]

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
