/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels

import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Transport of the completed tensor scalar comparison

Source: blueprint thm-coef-rational-verdier, paragraph 3, and
lem-coef-integral-finite-extension, evaluation and completion paragraphs.
(blueprint: lem-coef-rational-verdier-tensor-scalar-transport). -/

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
  integralOperationsGoodComplex DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh HomotopyCategory.quotient
  constructibleIntegralTensor integralScalarExtensionOfUniverses
  sfConstructibleIntegralScalarExtension integralTensorScalarComparison
attribute [local instance 100000] PurCompactSupport.coefficientSiteSmall
  PurCompactSupport.coefficientRingSheafify PurCompactSupport.coefficientAbSheafify
  PurCompactSupport.coefficientAbLocallyBijective
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

private theorem tensor_transport {C : Type*} [Category* C] (H : C × C ⥤ C)
    {A B C₁ K K₁ K₂ M M₁ M₂ : C}
    (ea : A ≅ B) (ua : B ≅ C₁) (ek : K ≅ K₁) (uk : K₁ ≅ K₂)
    (em : M ≅ M₁) (um : M₁ ≅ M₂) (s : A ⟶ H.obj (K, M)) :
    (ea.inv ≫ s ≫ H.map (Prod.mkHom ek.hom em.hom)) ≫
        H.map (Prod.mkHom uk.hom um.hom) =
      ua.hom ≫ (ea ≪≫ ua).inv ≫ s ≫
        H.map (Prod.mkHom (ek ≪≫ uk).hom (em ≪≫ um).hom) := by
  have hp : Prod.mkHom (ek.hom ≫ uk.hom) (em.hom ≫ um.hom) =
      Prod.mkHom ek.hom em.hom ≫ Prod.mkHom uk.hom um.hom := rfl
  simp only [Iso.trans_hom, Iso.trans_inv, hp, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (X : Scheme.{u})

set_option maxHeartbeats 400000 in
-- The scalar-model identifications have distinct but definitionally equal endpoints.
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- Factorization of scalar completion transports the completed tensor comparison.

Source: blueprint lem-coef-integral-finite-extension.proof.md, completion paragraph,
and the definition of scalarTensorCompleted.
(blueprint: lem-coef-rational-verdier-tensor-scalar-transport).

Proof: the assumed equality of natural transformations identifies scalarCompletionIso
on each complete object with e followed by the concrete completion isomorphism.
Substitute these three factorizations in the definition of scalarTensorCompleted.
Functoriality on the two inputs and cancellation of the completion on their tensor
then give the equation. This uses only completeness of the three objects, with no
tensor presentation, completion chain normalization, or localization argument. -/
theorem tensor_scalar_completion_transport
    (e : integralOrdinaryDerivedScalar l E L i X ≅
      completedDerivedScalarExtension.{u, u} l E L i X)
    (hχ : e.hom ≫ completedScalarComparison l E L i X = scalarCompletion l E L i X)
    (K M : DerivedCategory (integralTowerModules l E X))
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M)
    (hT : IsSfDerivedComplete l E X ((integralCompletedTensor l E X).obj (K, M))) :
    (Functor.isoWhiskerLeft (integralCompletedTensor l E X) e.symm ≪≫
        scalarTensorOrdinary l E L i X ≪≫
        Functor.isoWhiskerRight (NatIso.prod e e) (integralCompletedTensor l L X)).hom.app
          (K, M) ≫
      (integralCompletedTensor l L X).map (Prod.mkHom
        (IntegralFiniteExtension.completion l E L i X K hK).hom
        (IntegralFiniteExtension.completion l E L i X M hM).hom) =
    (IntegralFiniteExtension.completion l E L i X
      ((integralCompletedTensor l E X).obj (K, M)) hT).hom ≫
      (scalarTensorCompleted l E L i X K M hK hM hT).hom := by
  let F := pbcDerivedExtend (completedCoefficientMap l E L i X)
  change integralOrdinaryDerivedScalar l E L i X ≅ F at e
  have hs (N : DerivedCategory (integralTowerModules l E X))
      (hN : IsSfDerivedComplete l E X N) :
      scalarCompletionIso l E L i X N hN =
        e.app N ≪≫ IntegralFiniteExtension.completion l E L i X N hN := by
    apply Iso.ext
    change (scalarCompletion l E L i X).app N =
      e.hom.app N ≫ (completedScalarComparison l E L i X).app N
    exact (NatTrans.congr_app hχ N).symm
  dsimp only [scalarTensorCompleted]
  erw [hs, hs, hs]
  change (e.inv.app ((integralCompletedTensor l E X).obj (K, M)) ≫
      (scalarTensorOrdinary l E L i X).hom.app (K, M) ≫
      (integralCompletedTensor l L X).map
        (Prod.mkHom (e.hom.app K) (e.hom.app M))) ≫ _ = _
  exact tensor_transport (integralCompletedTensor l L X)
    (e.app ((integralCompletedTensor l E X).obj (K, M)))
    (IntegralFiniteExtension.completion l E L i X _ hT)
    (e.app K) (IntegralFiniteExtension.completion l E L i X K hK)
    (e.app M) (IntegralFiniteExtension.completion l E L i X M hM)
    ((scalarTensorOrdinary l E L i X).hom.app (K, M))

end WeilConjectures.RationalVerdier
