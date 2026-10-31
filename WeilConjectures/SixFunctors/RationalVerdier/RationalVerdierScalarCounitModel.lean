/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels

import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # The scalar counit in the two recorded cochain models

Source: the normalized completion and tensor calculations in the blueprint proof of
lem-coef-integral-finite-extension, paragraphs 1 and 4.
(blueprint: lem-coef-rational-verdier-scalar-counit-model).
-/

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
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local implicit_reducible] Functor.mapHomologicalComplex
  completedOrdinaryScalarComplex coefficientTotalTensor
  DerivedCategory.Q DerivedCategory.Qh HomologicalComplexUpToQuasiIso.Qh
  HomotopyCategory.quotient integralOperationsGoodComplex
  IntegralFiniteExtension.tensorModel
attribute [local instance 100000] PurCompactSupport.coefficientSiteSmall
  PurCompactSupport.coefficientRingSheafify PurCompactSupport.coefficientAbSheafify
  PurCompactSupport.coefficientAbLocallyBijective
  CategoryTheory.Limits.HasColimitsOfShape.has_colimit
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (X : Scheme.{u})

set_option maxHeartbeats 400000 in
-- The counit identifies quotient and homotopy-localization endpoints explicitly.
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- The concrete and recorded scalar counits agree on cochain representatives.
Source: Stacks 06YY and the recorded completed scalar model construction.
(blueprint: lem-coef-rational-verdier-scalar-counit-model).
Proof: the quotient-to-homotopy-category comparison and the termwise functor
comparison are identities on objects. Functoriality maps their identity
components to identities. Remove these identities from pbcComplexCounit;
the remaining homotopy-category counit is exactly completedScalarCounit. -/
theorem ordinary_scalar_counit_model (A : CochainComplex (integralTowerModules.{u, u} l E X) ℤ) :
    pbcComplexCounit (completedCoefficientMap.{u, u} l E L i X) A =
      completedScalarCounit.{u, u} l E L i X A := by
  let φ := completedCoefficientMap.{u, u} l E L i X
  unfold pbcComplexCounit
  have h₁ :
      (DerivedCategory.quotientCompQhIso.{u + 2} (integralTowerModules.{u, u} l E X)).inv.app A =
      𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso.{u + 2} (integralTowerModules.{u, u} l L X)).hom.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj A) = 𝟙 _ := rfl
  have h₃ : ((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom.app A = 𝟙 _ := rfl
  have hf : (pbcDerivedExtend φ).map
      ((DerivedCategory.quotientCompQhIso.{u + 2} _).inv.app A) = 𝟙 _ := by
    rw [h₁]
    exact (pbcDerivedExtend φ).map_id _
  have hq : DerivedCategory.Qh.{u + 2}.map
      (((pbcExtend φ).mapHomotopyCategoryFactors (.up ℤ)).hom.app A) = 𝟙 _ := by
    rw [h₃]
    exact DerivedCategory.Qh.{u + 2}.map_id _
  rw [hf, hq, h₂]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]
  rfl

end WeilConjectures.RationalVerdier
