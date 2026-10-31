/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGroup

/-!

# Generic automorphisms acting on the generic slice model

Let `M''` be the generic slice model of a trait model `M` over a generic base
(`NearbyCyclesModel.genericSliceModel`), with total space `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` and base
`X₂`. It has the same total space, geometric generic fibre and special fibre as the base change
`M ×_{𝔸¹_S} Spec K⟦t⟧` (`NearbyCyclesModel.baseChange`) of `M`, viewed as a model of `X₁`, but its
identification `ε` lands in `X₂`. So:

* a generic automorphism `σ` (`NearbyCyclesModel.GenericAut`) acts on `M''` by a morphism of models
  over the identities (`NearbyCyclesModel.genericSliceAut`), which is `σ` on `Spec Ω_K`;
* the identities of the total space and of the geometric generic fibre form a morphism of models
  `M'' ⟶ M ×_{𝔸¹_S} Spec K⟦t⟧` over `c : X₂ ⟶ X₁`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceToBaseChange`), whose composite with the
  projection of the base change is the projection of the generic slice model
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.genericSliceHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- A generic automorphism fixes the geometric generic point `Spec Ω_K ⟶ Spec Frac K⟦t⟧`. -/
@[reassoc (attr := simp)]
lemma GenericAut.τ_comp_traitGenericPointToSpec (σ : GenericAut k' K) :
    σ.τ ≫ traitGenericPointToSpec K = traitGenericPointToSpec K := by
  rw [← cancel_mono (traitGenericSpec K), Category.assoc, traitGenericPointToSpec_traitGenericSpec,
    σ.over_trait]

section Aut

variable (x : K) {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-- The action of a generic automorphism `σ` on the generic slice model: the morphism of models
over the identities which is the identity on the total space and `σ` on the geometric generic
fibre `𝒳'' ×_{K⟦t⟧} Spec Ω_K`. -/
@[simps]
noncomputable def genericSliceAut (σ : GenericAut k' K) :
    (genericSliceModel x hb).Hom (genericSliceModel x hb) (𝟙 _) (𝟙 _) where
  total := 𝟙 _
  generic := pullback.map _ _ _ _ (𝟙 _) σ.τ (𝟙 _) (by simp) (by simp [σ.over_trait])
  comm_j := by simp
  comm_i := by simp
  comm_ε := by
    simp only [genericSliceModel_ε, Category.comp_id]
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp

lemma genericSliceAut_generic_snd (σ : GenericAut k' K) :
    (genericSliceAut x hb σ).generic ≫ pullback.snd _ _ = pullback.snd _ _ ≫ σ.τ := by
  simp [genericSliceAut]

end Aut

section BaseChange

variable {F : Type u} [Field F] {X₁ : Over (Spec (.of F))} {X' : Over (Spec (.of k'))}
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (x : K)
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

namespace IsTraitModelOfGenericBase

/-- The morphism of models `M'' ⟶ M ×_{𝔸¹_S} Spec K⟦t⟧` from the generic slice model to the base
change, over `c : X₂ ⟶ X₁` and the identity of the special fibre: the identities of the total
space and of the geometric generic fibre. -/
@[simps]
noncomputable def genericSliceToBaseChange :
    (genericSliceModel x hb).Hom
      (baseChange h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x))
      (h.genericSliceBaseMap x hb) (𝟙 _) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by simp
  comm_i := by simp
  comm_ε := by
    rw [Category.id_comp, genericSliceModel_ε_comp_genericSliceBaseMap]
    rfl

instance : IsIso (h.genericSliceToBaseChange x hb).total := by
  rw [genericSliceToBaseChange_total]
  infer_instance

instance : IsIso (h.genericSliceToBaseChange x hb).generic := by
  rw [genericSliceToBaseChange_generic]
  infer_instance

lemma sliceSpecialMap_eq :
    sliceSpecialMap x h.isTraitModelOver hb =
      baseChangeSpecialMap h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x) :=
  h.isTraitModelOver.isPullback_i.hom_ext (by simp [sliceSpecialMap])
    (by simp [sliceSpecialMap, baseChangeSpecialMap])

lemma genericSliceToBaseChange_total_comp :
    (h.genericSliceToBaseChange x hb).total ≫
        (baseChangeHom h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x)).total =
      (h.genericSliceHom x hb).total := by
  simp [genericSliceHom]

lemma genericSliceToBaseChange_generic_comp :
    (h.genericSliceToBaseChange x hb).generic ≫
        (baseChangeHom h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x)).generic =
      (h.genericSliceHom x hb).generic := by
  simp [genericSliceHom]

lemma genericSliceAut_total_comp_genericSliceToBaseChange (σ : GenericAut k' K) :
    (genericSliceAut x hb σ).total ≫ (h.genericSliceToBaseChange x hb).total =
      (h.genericSliceToBaseChange x hb).total ≫
        (baseChangeAut h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x) σ).total := by
  simp

lemma genericSliceAut_generic_comp_genericSliceToBaseChange (σ : GenericAut k' K) :
    (genericSliceAut x hb σ).generic ≫ (h.genericSliceToBaseChange x hb).generic =
      (h.genericSliceToBaseChange x hb).generic ≫
        (baseChangeAut h.isTraitModelOver b hb (traitSlice x) (traitSlice_over x) σ).generic := by
  simp only [genericSliceToBaseChange_generic, Category.comp_id, Category.id_comp]
  rfl

end IsTraitModelOfGenericBase

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
