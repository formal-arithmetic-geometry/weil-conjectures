/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Tensor.AdicTensorPresentationComparison
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedModelExistence
import all WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveQuotientAugmentations
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The normalized tensor presentation is the reduction adjunct

Source: BS Definition 3.4.10; Stacks 07A4, 07A6 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

attribute [local implicit_reducible] PurCompactSupport.completed
  integralOperationsGoodLocalization integralOperationsGoodComplex integralOperationsTensorOnGood
  coefficientKFlatInclusion coefficientTotalTensor pullbackTensorReferenceTensor
attribute [local irreducible] SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  pullbackTensorCalculus pullbackTensorIntegralTensorModel integralCompletedTensorComparison
  coefficientSequenceLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private theorem presentation_model (N : ConstructibleTensorCompletionPresentation l E X)
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    N.model.hom.app (P, Q) ≫
        (tensorPresentationComparison l E X N).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      (pullbackTensorCalculus l E X).integralTensorModel.comparison.hom.app
        (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩) := by
  let q := integralOperationsGoodLocalization l E X
  let i := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) :
        ObjectProperty (CochainComplex (integralTowerModules l E X) ℤ))
    (integralOperationsGoodComplex l E X).ι (fun P ↦ P.property.1)
  let r : ((integralOperationsGoodComplex l E X).ι.prod
        (integralOperationsGoodComplex l E X).ι) ⋙ constructibleTensorTotal l E X ⋙
          DerivedCategory.Q ≅
      (q.prod q) ⋙ (pullbackTensorCalculus l E X).integralClosed.tensor :=
    Functor.isoWhiskerLeft (i.prod i)
      (pullbackTensorCalculus l E X).integralTensorModel.comparison
  have h : Functor.whiskerLeft (q.prod q) (tensorPresentationComparison l E X N).hom =
      (N.model.symm ≪≫ r).hom := by
    let H := (Functor.whiskeringLeft _ _
      (DerivedCategory (integralTowerModules l E X))).obj (q.prod q)
    let h := (SheafOfModules.cochain_tensor_model_rigidity (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X)).choose_spec.2.2
    let ff : H.FullyFaithful :=
      ((Functor.FullyFaithful.nonempty_iff_map_bijective H).2
        (fun U V ↦ h _ inferInstance U V)).some
    change H.map (ff.preimageIso (N.model.symm ≪≫ r)).hom = _
    exact ff.map_preimage _
  have hh := congrArg (fun z ↦ N.model.hom.app (P, Q) ≫ z.app (P, Q)) h
  simpa only [Functor.whiskerLeft_app, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_app_assoc, q, integralOperationsGoodLocalization,
    Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj, r,
    Functor.isoWhiskerLeft_hom, i, ObjectProperty.lift] using hh

private theorem presentation_normalized (N : ConstructibleTensorCompletionPresentation l E X) :
    StrictTensorAugmentation.Normalized l E X N.cochain := by
  constructor
  · exact N.normalized.1
  · intro P Q i
    exact N.normalized.2.1 P Q i (i - 1) (by omega)

private theorem ringed_normalized (d : IntegralSystemRealization.RingedModels l E)
    (X : Scheme.{u}) :
    StrictTensorAugmentation.Normalized l E X (d.tensor X).chain := by
  constructor
  · exact (d.tensor X).canonical.1.1
  · intro P Q i
    exact (d.tensor X).canonical.1.2 P Q i (i - 1) (by omega)

private theorem presentation_chain (N : ConstructibleTensorCompletionPresentation l E X)
    (d : IntegralSystemRealization.RingedModels l E) : N.cochain = (d.tensor X).chain := by
  apply (StrictTensorAugmentation.existsUnique_normalized l E X).unique
  · exact presentation_normalized l E X N
  · exact ringed_normalized l E d X

set_option maxHeartbeats 2000000 in
-- Comparing the two localized tensor models requires a larger elaboration budget.
/-- Every normalized presentation gives the adjunct of the specified coherent
reduction tensor comparison, expressed on the fixed ambient tensor.
Source: BS Definition 3.4.10; Stacks 07A4, 07A6 and 0941.
(blueprint: lem-sf-adic-tensor-presentation-augmentation).

Proof: fully faithful restriction to good pairs identifies the presentation
comparison with the comparison of the recorded total tensors. The two coordinates
of the strict augmentation identify its cochain map with the ringed model's map.
Its representative descent equation therefore identifies the two derived
augmentations. The ringed model's quotient-adjunction formula identifies this map
with the reduction unit followed by reductionTensor and the inverse tensor
realization. Naturality of the unit cancels the ordinary tensor-model comparison.
Faithful restriction gives the formula on every ambient pair, including zero pairs. -/
theorem tensorPresentationCompletion_augmentation
    (N : ConstructibleTensorCompletionPresentation l E X)
    (M L : DerivedCategory (integralTowerModules l E X)) :
    (tensorPresentationCompletion l E X N).app (M, L) ≫
        (pullbackTensorIntegralTensorModel l E X).hom.app (M, L) =
      (pullbackTensorCalculus l E X).adjunction.unit.app
          ((pullbackTensorCalculus l E X).integralClosed.tensor.obj (M, L)) ≫
        (coefficientSequenceLimit l E X).map
          ((pullbackTensorCalculus l E X).reductionTensor.hom.app (M, L)) := by
  obtain ⟨d, _⟩ := IntegralSystemRealization.integralRingedModelExistence l E
  let S := pullbackTensorCalculus l E X
  let R := coefficientSequenceLimit l E X
  let T := S.integralClosed.tensor
  let a : (d.tensor X).ordinary.tensor ≅ T := eqToIso (d.tensorClosed X)
  let τ : T ⟶ integralCompletedTensor l E X := a.inv ≫ (d.tensor X).chi l E
  let q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  have hτ : tensorPresentationCompletion l E X N = τ := by
    apply Localization.natTrans_ext (q.prod q) (W.prod W)
    rintro ⟨P, Q⟩
    let e := (tensorPresentationComparison l E X N).app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
    let r : DerivedCategory.Q.obj ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ⟶
        T.obj (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) :=
      S.integralTensorModel.comparison.hom.app
        (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩)
    have hr : N.model.hom.app (P, Q) ≫ e.hom = r :=
      presentation_model l E X N P Q
    have hd := d.tensorRepresentative X P.obj Q.obj P.property Q.property
    have hd' : (d.tensor X).ordinary.representative.hom.app
        (⟨P.obj, P.property⟩, ⟨Q.obj, Q.property⟩) ≫ a.hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) = r := by
      simpa only [a, T, S, IntegralSystemRealization.calculus, eqToIso.hom,
        eqToHom_app, CoefficientTensorModels.iso, Iso.app_hom] using hd
    apply (cancel_epi r).1
    apply (cancel_mono ((integralCompletedTensorComparison l E X).hom.app (P, Q))).1
    change (r ≫ (e.inv ≫ N.comparison.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))) ≫ _ =
      (r ≫ τ.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫ _
    rw [← hr]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [N.normalized.2.2.1 P Q]
    rw [presentation_chain l E X N d]
    rw [← Category.assoc (N.model.hom.app (P, Q)) e.hom, hr, ← hd']
    simpa only [τ, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc,
      OpenFactorCoherence.Tensor.chi, Functor.whiskerLeft_app] using
        ((d.tensor X).canonical.2 P.obj Q.obj P.property Q.property).symm
  let α := tensorPresentationCompletion l E X N ≫
    (pullbackTensorIntegralTensorModel l E X).hom
  let β := Functor.whiskerLeft T S.adjunction.unit ≫
    Functor.whiskerRight S.reductionTensor.hom R
  have hab : α = β := by
    apply Localization.natTrans_ext (q.prod q) (W.prod W)
    rintro ⟨P, Q⟩
    have hd := GeneratorReduction.tensor_augmentation_onGood l E d X P Q
    have hd' : ((d.tensor X).chi l E).app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (pullbackTensorIntegralTensorModel l E X).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      S.adjunction.unit.app ((d.tensor X).ordinary.tensor.obj
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      R.map (S.reduction.map (a.hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
        S.reductionTensor.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) := by
      simpa only [a, eqToIso.hom, eqToHom_app, S, IntegralSystemRealization.calculus, R]
        using hd
    have hn := S.adjunction.unit.naturality (a.inv.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    dsimp only [α, NatTrans.comp_app]
    rw [hτ]
    change (a.inv.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      ((d.tensor X).chi l E).app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      (pullbackTensorIntegralTensorModel l E X).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      β.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
    rw [Category.assoc, hd']
    rw [R.map_comp, ← Category.assoc, hn]
    simp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc]
    change S.adjunction.unit.app (T.obj
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
      R.map (S.reduction.map (a.inv.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))) ≫
      R.map (S.reduction.map (a.hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))) ≫
      R.map (S.reductionTensor.hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) = _
    rw [← R.map_comp_assoc, ← S.reduction.map_comp, Iso.inv_hom_id_app,
      S.reduction.map_id, R.map_id, Category.id_comp]
  exact congrArg (fun z ↦ z.app (M, L)) hab

end WeilConjectures.AdicQbarRealization
