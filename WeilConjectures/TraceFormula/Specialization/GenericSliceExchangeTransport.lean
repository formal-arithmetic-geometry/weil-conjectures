/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceModelAut
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerMap

/-!

# The exchange of the generic slice model and of the base change

Let `M` be a trait model over a generic base, `M''` its generic slice model
(`NearbyCyclesModel.genericSliceModel`) and `M_σ = M ×_{𝔸¹_S} Spec K⟦t⟧` the base change of `M`
along the generic slice (`NearbyCyclesModel.baseChange`). The projection `M'' ⟶ M` is the
composite of `M'' ⟶ M_σ` (the identities of the total space and of the geometric generic fibre,
`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceToBaseChange`) and of the projection
`M_σ ⟶ M`. The first has an invertible exchange, which intertwines the actions of the generic
automorphisms. Hence the exchange `α_χ` of `M'' ⟶ M` at `C` is, up to isomorphisms `U` and `W`,
the exchange `α_β` of `M_σ ⟶ M`, and `W` conjugates the actions on `Ψ_{M_σ}` into those on
`Ψ_{M''}`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_pullbackExchange_genericSliceHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]
  {F : Type u} [Field F] {X₁ : Over (Spec (.of F))} {X' : Over (Spec (.of k'))}
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (x : K)
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace IsTraitModelOfGenericBase

set_option maxHeartbeats 1600000 in
-- the exchanges of the three models are large terms
/-- **The exchange of the generic slice model is the exchange of the base change**, up to
isomorphisms: `α_χ = U ≫ α_β ≫ W` for the exchanges `α_χ` of the projection `M'' ⟶ M` from the
generic slice model and `α_β` of the projection `M ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ M` from the base change,
and `W` conjugates the action of each generic automorphism `σ` on the nearby cycles of the base
change into its action on the nearby cycles of the generic slice model. -/
theorem exists_iso_pullbackExchange_genericSliceHom
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁.left) Ab.{u + 1})
      (condensedRingObj Λ X₁.left))) :
    ∃ (U : L((sliceSpecialMap x h.isTraitModelOver hb)^*⟦Λ⟧).obj ((M.nearbyCycles Λ).obj C) ≅
        L((baseChangeSpecialMap h.isTraitModelOver b hb (traitSlice x)
          (traitSlice_over x))^*⟦Λ⟧).obj ((M.nearbyCycles Λ).obj C))
      (W : ((baseChange h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x)).nearbyCycles
          Λ).obj (L((𝟙 X₁.left)^*⟦Λ⟧).obj C) ≅
        ((genericSliceModel x hb).nearbyCycles Λ).obj
          (L((h.genericSliceBaseMap x hb)^*⟦Λ⟧).obj C)),
      ((h.genericSliceHom x hb).pullbackExchange Λ).app C =
          U.hom ≫ ((baseChangeHom h.isTraitModelOver b hb (traitSlice x)
            (traitSlice_over x)).pullbackExchange Λ).app C ≫ W.hom ∧
        ∀ σ : GenericAut k' K,
          (genericSliceAut x hb σ).autAction Λ (L((h.genericSliceBaseMap x hb)^*⟦Λ⟧).obj C) =
            W.inv ≫ (baseChangeAut h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x)
              σ).autAction Λ (L((𝟙 X₁.left)^*⟦Λ⟧).obj C) ≫ W.hom := by
  have h' : 𝟙 _ ≫ baseChangeSpecialMap h.isTraitModelOver b hb (traitSlice x)
      (traitSlice_over x) = sliceSpecialMap x h.isTraitModelOver hb := by
    rw [Category.id_comp, sliceSpecialMap_eq x h hb]
  have hx := (h.genericSliceToBaseChange x hb).pullbackExchange_comp_app_of_eq Λ
    (baseChangeHom h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x))
    (h.genericSliceHom x hb) (Category.comp_id _) h'
    (genericSliceToBaseChange_total_comp x h hb) (genericSliceToBaseChange_generic_comp x h hb) C
  have := Hom.isIso_pullbackExchange_of_isIso Λ (h.genericSliceToBaseChange x hb)
  let I := leftDerivedUpperStarId Λ (baseChangeSpecial b (traitSlice x)).left
  let E := leftDerivedUpperStarCompOfEq Λ (Category.comp_id (h.genericSliceBaseMap x hb))
  let W := I.symm.app _ ≪≫
    asIso (((h.genericSliceToBaseChange x hb).pullbackExchange Λ).app
      (L((𝟙 X₁.left)^*⟦Λ⟧).obj C)) ≪≫
    ((genericSliceModel x hb).nearbyCycles Λ).mapIso (E.app C).symm
  refine ⟨(leftDerivedUpperStarCompOfEq Λ h').app _ ≪≫ I.app _, W, ?_, fun σ ↦ ?_⟩
  · have hx' := (Iso.comp_inv_eq
      (((genericSliceModel x hb).nearbyCycles Λ).mapIso (E.app C))).mpr hx.symm
    have hI := I.hom.naturality (((baseChangeHom h.isTraitModelOver b hb (traitSlice x)
      (traitSlice_over x)).pullbackExchange Λ).app C)
    dsimp only [Functor.id_map] at hI
    rw [← hx']
    simp only [W, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, asIso_hom,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    rw [← reassoc_of% hI, Iso.hom_inv_id_app_assoc]
  · rw [Iso.eq_inv_comp]
    have hc := (h.genericSliceToBaseChange x hb).pullbackExchange_app_comp_autAction_of_comm Λ
      (genericSliceAut x hb σ)
      (baseChangeAut h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x) σ)
      (genericSliceAut_total_comp_genericSliceToBaseChange x h hb σ)
      (genericSliceAut_generic_comp_genericSliceToBaseChange x h hb σ)
      (L((𝟙 X₁.left)^*⟦Λ⟧).obj C)
    have hI := I.inv.naturality ((baseChangeAut h.isTraitModelOver b hb (traitSlice x)
      (traitSlice_over x) σ).autAction Λ (L((𝟙 X₁.left)^*⟦Λ⟧).obj C))
    dsimp only [Functor.id_map] at hI
    have hn : (genericSliceAut x hb σ).autAction Λ
          (L((h.genericSliceBaseMap x hb)^*⟦Λ⟧).obj (L((𝟙 X₁.left)^*⟦Λ⟧).obj C)) ≫
        ((genericSliceModel x hb).nearbyCycles Λ).map (E.inv.app C) =
      ((genericSliceModel x hb).nearbyCycles Λ).map (E.inv.app C) ≫
        (genericSliceAut x hb σ).autAction Λ (L((h.genericSliceBaseMap x hb)^*⟦Λ⟧).obj C) :=
      (genericSliceAut x hb σ).autAction_naturality Λ (E.inv.app C)
    simp only [W, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom,
      Iso.app_inv, Category.assoc]
    rw [← hn, reassoc_of% hc]
    exact ((reassoc_of% hI) _).symm

end IsTraitModelOfGenericBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
