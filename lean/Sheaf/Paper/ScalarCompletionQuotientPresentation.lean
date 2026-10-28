/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ScalarExtensionTowerRealizationData

/-! # Coherent quotient presentations and scalar completion

Source: Stacks 06YY and 0941. This isolates the source-side presentation
transport in the scalar/pullback realization calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Scalar completion induces the coherent quotient presentation of ordinary scalar change.
Source: Stacks 06YY, 0941; scalar normalization and the tensor-unit augmentation
in step 1 of stage3-pur-scalar-pullback-left-roos.
(blueprint: lem-pur-scalar-completion-quotient-presentation).

Proof: choose ordinary quotient models for the good complexes P and its ordinary
scalar extension PS, with their normalized derived reduction presentations (the
coherent primitive presentation construction). Coherence of (C,eC,kappa) identifies
C with the first ordinary model. Associate, level by level, quotient scalar tensors
with the quotient of ordinary scalar extension. These associations commute with
differentials and every quotient transition, so they give an isomorphism from CS
to the ordinary quotient model of PS. Transport its normalized comparison and finite
identifications back along this isomorphism to obtain eS and kappaS. The balanced
associators send nested unit tensors to 1 tensor (1 tensor x), proving the section
formula. Their tensor-unit maps also agree before localization, so transporting the
ordinary adjunction transpose gives both reduction-presentation and whole-system
coherence equations. Finally apply the reduction/total-limit adjunction to the last
equality. Scalar normalization of SY identifies its realized side with the scalar
representative comparison. ScalarCompletionNormalization identifies the ordinary
scalar source augmentation with that same comparison composed with scalarCompletion.
The ordinary constant-tower/limit unit and counit identities then identify the two
transposes. Injectivity of the adjunction equivalence proves the last displayed
equality in the derived category of the entire sequence site; no faithfulness of
individual derived evaluations is used.
No pullback, derived completeness, invertibility of l on Y or flatness of a finite
quotient coefficient map is used. Empty sites, zero complexes, identity embeddings,
n=0 and ramified embeddings have the same balanced tensor association. -/
theorem scalarCompletionQuotientPresentation (Y : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (ρ : IntegralComparisonRoosModel.{u, u} l L Y)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι Y SE ρ)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E Y
      SE.toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E Y SE P.obj C eC κ) :
    let PS := ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj
    let CS := ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
      (.up ℤ)).obj C
    ∃ (eS : SL.reduction.obj (DerivedCategory.Q.obj PS) ≅ DerivedCategory.Q.obj CS)
      (κS : ∀ n : ℕ,
        ((coefficientSequenceEvaluation.{u, u} l L Y n).mapHomologicalComplex (.up ℤ)).obj CS ≅
          (unrestrictedIntegralFiniteComplex.{u, u} l L Y n).obj PS),
      CoefficientReductionPresentation.{u, u} l L Y SL.toCoefficientDerivedSystemReduction
        PS (scalarGood l E L ι Y P).1 CS eS κS ∧
      IsIntegralComparisonPresentationCoherent.{u, u} l L Y SL PS CS eS κS ∧
      (∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (P.obj.X i).val.obj (op U)),
        ((κS n).hom.f i).val.app (op U)
          (coefficientEvaluationSection.{u, u} l L Y (CS.X i) n (op U)
            (integralComparisonSequenceTensorSection.{u, u} l E L ι Y (C.X i)
              (op (n, U)) 1
              (integralComparisonSequenceSection.{u, u} l E Y (C.X i) n (op U)
                (((κ n).inv.f i).val.app (op U)
                  (unrestrictedIntegralTensorSection.{u, u} l E Y n (P.obj.X i)
                    (op U) 1 x))))) =
          unrestrictedIntegralTensorSection.{u, u} l L Y n (PS.X i) (op U) 1
            (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) (op U) 1 x)) ∧
      SL.reduction.map
          ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
        eS.hom =
      SL.reduction.map ((scalarCompletion l E L ι Y).app (DerivedCategory.Q.obj P.obj)) ≫
        scalarReduction l E L ι Y SE SL ρ SY (DerivedCategory.Q.obj P.obj) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι Y).map eC.hom ≫
        (integralComparisonSequenceScalarModel.{u, u} l E L ι Y).ε.app C := by
  sorry

end WeilConjectures.ScalarExtensionTower
