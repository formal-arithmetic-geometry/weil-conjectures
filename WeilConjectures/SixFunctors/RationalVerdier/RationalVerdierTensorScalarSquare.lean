/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels

import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierTensorScalarChain
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierOrdinaryScalarTensorRepresentative
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Descent of the tensor scalar/completion square

Source: blueprint thm-coef-rational-verdier, paragraph 3, and
lem-coef-integral-finite-extension, evaluation and completion paragraphs.
(blueprint: lem-coef-rational-verdier-tensor-scalar-square). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

attribute [local irreducible] HasDerivedCategory.standard
  integralCompletedTensor integralCompletedTensorComparison
  integralOperationsTensorComplexFunctor integralOrdinaryScalar
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  PurCompactSupport.scalarTensor PurCompactSupport.scalarTensorTotal
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local implicit_reducible] Functor.mapHomologicalComplex
  completedOrdinaryScalarComplex coefficientTotalTensor IntegralFiniteExtension.tensorModel
  CategoryTheory.uniformProd CategoryTheory.prod' CategoryTheory.prod
  integralOperationsGoodComplex integralOperationsGoodLocalization
  integralOperationsTensorOnGood DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh HomotopyCategory.quotient
  constructibleIntegralTensor integralScalarExtensionOfUniverses
  sfConstructibleIntegralScalarExtension integralTensorScalarComparison
attribute [local instance 100000] PurCompactSupport.coefficientSiteSmall
  PurCompactSupport.coefficientRingSheafify PurCompactSupport.coefficientAbSheafify
  PurCompactSupport.coefficientAbLocallyBijective
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

set_option maxHeartbeats 600000 in
-- The localization descent compares the two large tensor representative models explicitly.
omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] in
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- The normalized scalar/completion tensor square descends from good complexes.

Source: blueprint lem-coef-integral-finite-extension.proof.md, completion paragraph,
and thm-coef-rational-verdier.proof.md, paragraph 3.
(blueprint: lem-coef-rational-verdier-tensor-scalar-square).

Proof: precompose both natural transformations with the product of the good-complex
localizations. The representative formula for each completion, compatibility of the
ordinary scalar tensorator with representatives, and the chain-level completion square
identify their composites with the same map. Cancel the representative isomorphism on
the source and the completed-tensor comparison on the target. Naturality of the
ordinary-to-derived scalar comparison supplies the remaining coordinate change.
Localization detects equality of these natural transformations. -/
theorem tensor_completion_scalar_square
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (cE : Completion D l hl X E a) (cL : Completion D l hl X L b)
    (t : integralOrdinaryScalar l E L i X ≅
      completedOrdinaryScalarExtension.{u, u} l E L i X)
    (e : integralOrdinaryDerivedScalar l E L i X ≅
      completedDerivedScalarExtension.{u, u} l E L i X)
    (ht : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : N.val.obj U),
      (t.hom.app N).val.app U (integralOrdinaryTensorSection l E L i X N U s x) =
        completedScalarTensorSection.{u, u} l E L i X N U s x)
    (he : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L i X P =
        (integralOrdinaryScalar l E L i X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex t (.up ℤ)).hom.app P)) :
    (PurCompactSupport.scalarTensor (completedCoefficientMap l E L i X)
      (IntegralFiniteExtension.tensorModel X a)
      (IntegralFiniteExtension.tensorModel X b)).hom ≫
        Functor.whiskerLeft
          ((pbcDerivedExtend (completedCoefficientMap l E L i X)).prod
            (pbcDerivedExtend (completedCoefficientMap l E L i X))) cL.map =
    Functor.whiskerRight cE.map (pbcDerivedExtend (completedCoefficientMap l E L i X)) ≫
      (Functor.isoWhiskerLeft (integralCompletedTensor l E X) e.symm ≪≫
        scalarTensorOrdinary l E L i X ≪≫
        Functor.isoWhiskerRight (NatIso.prod e e) (integralCompletedTensor l L X)).hom := by
  let F := pbcDerivedExtend (completedCoefficientMap l E L i X)
  change integralOrdinaryDerivedScalar l E L i X ≅ F at e
  change integralOrdinaryScalar l E L i X ≅
    pbcExtend (completedCoefficientMap l E L i X) at t
  let O := integralOrdinaryScalar l E L i X
  let δ := Functor.whiskerLeft DerivedCategory.Q e.inv ≫ O.mapDerivedCategoryFactors.hom
  let γ := Functor.isoWhiskerLeft (integralCompletedTensor l E X) e.symm ≪≫
    scalarTensorOrdinary l E L i X ≪≫
    Functor.isoWhiskerRight (NatIso.prod e e) (integralCompletedTensor l L X)
  let μ := PurCompactSupport.scalarTensor (completedCoefficientMap l E L i X)
    (IntegralFiniteExtension.tensorModel X a) (IntegralFiniteExtension.tensorModel X b)
  let q := integralOperationsGoodLocalization l E X
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E X
  apply Localization.natTrans_ext (q.prod q) (V.prod V)
  rintro ⟨P, Q⟩
  let SP : (integralOperationsGoodComplex l L X).FullSubcategory :=
    ⟨_, scalarGood l E L i X P⟩
  let SQ : (integralOperationsGoodComplex l L X).FullSubcategory :=
    ⟨_, scalarGood l E L i X Q⟩
  let d := Prod.mkHom (δ.app P.obj) (δ.app Q.obj)
  let rE : (integralCompletedTensor l E X).obj (q.obj P, q.obj Q) ⟶
      DerivedCategory.Q.obj ((integralOperationsTensorComplexFunctor l E X).obj
        (P.obj, Q.obj)) := (integralCompletedTensorComparison l E X).hom.app (P, Q)
  let rL : (integralCompletedTensor l L X).obj
      (DerivedCategory.Q.obj SP.obj, DerivedCategory.Q.obj SQ.obj) ⟶
      DerivedCategory.Q.obj ((integralOperationsTensorComplexFunctor l L X).obj
        (SP.obj, SQ.obj)) := (integralCompletedTensorComparison l L X).hom.app (SP, SQ)
  let aP : DerivedCategory.Q.obj ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ⟶
      a.tensor.obj (q.obj P, q.obj Q) :=
    a.representative.hom.app (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩)
  let bP : DerivedCategory.Q.obj ((constructibleTensorTotal l L X).obj (SP.obj, SQ.obj)) ⟶
      b.tensor.obj (DerivedCategory.Q.obj SP.obj, DerivedCategory.Q.obj SQ.obj) :=
    b.representative.hom.app (⟨SP.obj, SP.property.1⟩, ⟨SQ.obj, SQ.property.1⟩)
  have hE : aP ≫ cE.map.app (q.obj P, q.obj Q) ≫ rE =
      DerivedCategory.Q.map ((completionChain D l hl X E).app (P.obj, Q.obj)) :=
    eq_of_heq (cE.representative P Q)
  have hL : bP ≫ cL.map.app (DerivedCategory.Q.obj SP.obj, DerivedCategory.Q.obj SQ.obj) ≫ rL =
      DerivedCategory.Q.map ((completionChain D l hl X L).app (SP.obj, SQ.obj)) :=
    eq_of_heq (cL.representative SP SQ)
  have hμ := ordinary_scalar_tensor_representative l E L i X a b t e ht he P Q
  change F.map aP ≫ μ.hom.app (q.obj P, q.obj Q) ≫ b.tensor.map d =
    δ.app ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L i X).hom.app
        (P.obj, Q.obj)) ≫ bP at hμ
  have hn := cL.map.naturality d
  change b.tensor.map d ≫ cL.map.app (DerivedCategory.Q.obj SP.obj, DerivedCategory.Q.obj SQ.obj) =
    cL.map.app (F.obj (q.obj P), F.obj (q.obj Q)) ≫
      (integralCompletedTensor l L X).map d at hn
  have hγ : γ.hom.app (q.obj P, q.obj Q) ≫
      (integralCompletedTensor l L X).map d ≫ rL =
    F.map rE ≫ δ.app ((integralOperationsTensorComplexFunctor l E X).obj
      (P.obj, Q.obj)) ≫ DerivedCategory.Q.map (scalarTensorChain l E L i X P.obj Q.obj) := by
    have hnorm := (scalarTensorOrdinary_existsUnique l E L i X).exists.choose_spec P Q
    change (integralOrdinaryDerivedScalar l E L i X).map rE ≫
        O.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map (scalarTensorChain l E L i X P.obj Q.obj) =
      (scalarTensorOrdinary l E L i X).hom.app (q.obj P, q.obj Q) ≫
        (integralCompletedTensor l L X).map
          (Prod.mkHom (O.mapDerivedCategoryFactors.hom.app P.obj)
            (O.mapDerivedCategoryFactors.hom.app Q.obj)) ≫ rL at hnorm
    have hd : (Prod.mkHom (e.hom.app (q.obj P)) (e.hom.app (q.obj Q))) ≫ d =
        Prod.mkHom (O.mapDerivedCategoryFactors.hom.app P.obj)
          (O.mapDerivedCategoryFactors.hom.app Q.obj) := by
      apply Prod.hom_ext
      · change e.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (e.inv.app (DerivedCategory.Q.obj P.obj) ≫ O.mapDerivedCategoryFactors.hom.app P.obj) =
          O.mapDerivedCategoryFactors.hom.app P.obj
        exact e.hom_inv_id_app_assoc _ _
      · change e.hom.app (DerivedCategory.Q.obj Q.obj) ≫
          (e.inv.app (DerivedCategory.Q.obj Q.obj) ≫ O.mapDerivedCategoryFactors.hom.app Q.obj) =
          O.mapDerivedCategoryFactors.hom.app Q.obj
        exact e.hom_inv_id_app_assoc _ _
    dsimp only [γ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.prod_hom,
      NatTrans.prod]
    erw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, hd, ← hnorm]
    have he' := e.inv.naturality rE
    change F.map rE ≫ e.inv.app _ = e.inv.app _ ≫
      (integralOrdinaryDerivedScalar l E L i X).map rE at he'
    dsimp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app]
    erw [← Category.assoc, ← he']
    simp only [Category.assoc]
  change μ.hom.app (q.obj P, q.obj Q) ≫
      cL.map.app (F.obj (q.obj P), F.obj (q.obj Q)) =
    F.map (cE.map.app (q.obj P, q.obj Q)) ≫ γ.hom.app (q.obj P, q.obj Q)
  let w := (integralCompletedTensor l L X).mapIso (Iso.prod
      (e.symm.app (DerivedCategory.Q.obj P.obj) ≪≫ O.mapDerivedCategoryFactors.app P.obj)
      (e.symm.app (DerivedCategory.Q.obj Q.obj) ≪≫ O.mapDerivedCategoryFactors.app Q.obj)) ≪≫
    (integralCompletedTensorComparison l L X).app (SP, SQ)
  let v := F.mapIso (a.representative.app
    (⟨P.obj, P.property.1⟩, ⟨Q.obj, Q.property.1⟩))
  apply (cancel_epi v.hom).mp
  apply (cancel_mono w.hom).mp
  change (F.map aP ≫ μ.hom.app (q.obj P, q.obj Q) ≫
      cL.map.app (F.obj (q.obj P), F.obj (q.obj Q))) ≫
      ((integralCompletedTensor l L X).map d ≫ rL) =
    (F.map aP ≫ F.map (cE.map.app (q.obj P, q.obj Q)) ≫
      γ.hom.app (q.obj P, q.obj Q)) ≫ ((integralCompletedTensor l L X).map d ≫ rL)
  simp only [Category.assoc]
  erw [← reassoc_of% hn, reassoc_of% hμ, hL]
  erw [← Functor.map_comp, ← tensor_completion_scalar_chain l E L i X D hl P.obj Q.obj,
    Functor.map_comp]
  erw [← reassoc_of% (δ.naturality
    ((completionChain D l hl X E).app (P.obj, Q.obj)))]
  erw [← hE, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  erw [hγ]

end WeilConjectures.RationalVerdier
