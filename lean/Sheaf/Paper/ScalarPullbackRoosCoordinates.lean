/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ScalarExtensionTowerRealizationData
import all Sheaf.Paper.IntegralGoodQuotientPresentation
import all Sheaf.Paper.IntegralComparisonSequenceSystems

/-! # Fixed cochain coordinates for the scalar/pullback calculation

Source: Stacks 06YY, 07A4 and 0941. The coordinates are constructed from the
ordinary scalar/pullback chain map and a coherent quotient presentation.
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

/-- The quotient comparison is fixed by the nested tensor-unit/pullback generators.
Source: Stacks 06YY, 07A4 (blueprint: stage3-pur-scalar-pullback-roos-coordinates). -/
def ScalarPullbackQuotientFormula
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) : Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (P.obj.X i).val.obj (op U)),
    ((q.hom.app (op n)).f i).val.app (op ((Scheme.proEtaleBaseChange f).obj U))
      (integralComparisonRestrictedSection.{u, u} l L X
        ((integralComparisonSequencePullback.{u, u} l L f).obj
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj (C.X i))) n
        (op ((Scheme.proEtaleBaseChange f).obj U))
        (integralComparisonSequenceGenerator.{u, u} l L f
          ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.obj (C.X i)) n U
          (integralComparisonSequenceTensorSection.{u, u} l E L ι Y (C.X i)
            (op (n, U)) 1
            (integralComparisonSequenceSection.{u, u} l E Y (C.X i) n (op U)
              (((κ n).inv.f i).val.app (op U)
                (unrestrictedIntegralTensorSection.{u, u} l E Y n (P.obj.X i)
                  (op U) 1 x)))))) =
      integralOperationsPullbackGenerator.{u, u} l L f n
        (((unrestrictedIntegralFiniteComplex.{u, u} l L Y n).obj
          (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)).X i)
        U (unrestrictedIntegralTensorSection.{u, u} l L Y n
          ((integralOrdinaryScalar l E L ι Y).obj (P.obj.X i)) (op U) 1
          (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) (op U) 1 x))

/-- Transport a whole-system map to fixed strict Roos coordinates.
Every factor is specified; no realization model of scalar extension or pullback
occurs in this construction.
Source: Stacks 06YY, 0941 (blueprint: stage3-pur-scalar-pullback-roos-coordinates). -/
def scalarPullbackRoosCoordinate
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (ρ : IntegralComparisonRoosModel.{u, u} l L X)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (eP : DerivedCategory.Q.obj P.obj ≅ K)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) :
    (coefficientSequenceLimit.{u, u} l L X).obj
      ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι X).obj
        ((integralComparisonDerivedSequencePullback.{u, u} l E f).obj (SE.reduction.obj K))) ⟶
      DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) :=
  (coefficientSequenceLimit.{u, u} l L X).map
    ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι X).map
        ((integralComparisonDerivedSequencePullback.{u, u} l E f).map
          (SE.reduction.map eP.inv ≫ eC.hom)) ≫
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι X).map
        ((integralComparisonSequencePullback.{u, u} l E f).mapDerivedCategoryFactors.hom.app C) ≫
      (integralComparisonSequenceScalarModel.{u, u} l E L ι X).ε.app
        (((integralComparisonSequencePullback.{u, u} l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (integralComparisonSequenceScalarPullback.{u, u} l E L ι f) (.up ℤ)).hom.app C)) ≫
    (integralComparisonRoosBridge.{u, u} l L X ρ _).hom ≫
    DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)

/-- The fixed ordinary scalar/pullback chain map, transported only at its source.
Source: Stacks 07A4, 0941 (blueprint: stage3-pur-scalar-pullback-roos-coordinates). -/
def scalarPullbackRoosChain {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (eP : DerivedCategory.Q.obj P.obj ≅ K)
    (hF : IsSfDerivedComplete l E X ((integralDerivedPullback.{u, u} l E f).obj K)) :
    (integralScalarExtension.{u} l E L ι X).obj
        ((integralDerivedPullback.{u, u} l E f).obj K) ⟶
      DerivedCategory.Q.obj ((integralOperationsPullbackComplexFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) :=
  (scalarCompletionIso l E L ι X _ hF).inv ≫
    (integralOrdinaryDerivedScalar l E L ι X).map
      ((integralDerivedPullback.{u, u} l E f).map eP.inv) ≫
    (integralOrdinaryDerivedScalar l E L ι X).map
      ((integralDerivedPullbackComparison.{u, u} l E f).hom.app P) ≫
    (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app
      ((integralOperationsPullbackComplexFunctor.{u, u} l E f).obj P.obj) ≫
    DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj)

/-- The nested scalar/pullback strict quotient coordinates exist.
This statement involves no completed
comparison map and no scalar or pullback realization model.
Source: Stacks 06YY, 07A4 and 0941; the quotient and localization parts of step 8
of lem-pur-scalar-extension-tower-coherence.
(blueprint: stage3-pur-scalar-pullback-roos-coordinates).

Proof: compare C with the ordinary quotient system using whole-system coherence.
At level n associate B_n tensor over A_n (A_n tensor P) with B_n tensor P, and
identify this with B_n tensor over the completed B ring (B tensor P). Pull back
this association, retaining the actual quotient transitions, and restrict to the
completed coefficient ring. The resulting isomorphism is q. Both associations
send the three unit factors to the same generator, giving the displayed formula.
The construction is ordinary tensor association and uses no flatness of B_n over A_n;
zero P, n=0, identity maps, empty sites and ramified inclusions use the same tensors. -/
theorem scalarPullbackRoosCoordinates_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E Y SE.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E Y SE P.obj C eC κ) :
    ∃ q :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj),
      ScalarPullbackQuotientFormula l E L ι f P C κ q := by
  sorry

/-- Scalar derived extension computes on the pulled coherent quotient complex.
Source: Stacks 06YY and 07A4
(blueprint: stage3-pur-scalar-pullback-roos-coordinates).

Evaluation identifies C with the finite scalar extensions of P. K-flatness and
flatness pass through these isomorphisms and are detected on the sequence site.
Exact inverse image preserves this resolving class; the scalar model computes. -/
theorem scalarPullbackQuotient_computes {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj) :
    IsIso ((integralComparisonSequenceScalarModel.{u, u} l E L ι X).ε.app
      (((integralComparisonSequencePullback.{u, u} l E f).mapHomologicalComplex (.up ℤ)).obj
        C)) := by
  have hk : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E Y) C := by
    apply WeilConjectures.kflat_of_levels l E Y
    intro n
    exact SheafOfModules.kFlat_iso_independent (integralCoefficientCommRingSheaf l E Y n)
      (κ n).symm ((coefficientTensorModelPreservation l E Y).1 P.obj P.property.1 n)
  have hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf.{u, u} l E Y) (C.X i) := by
    intro i
    apply WeilConjectures.flat_of_levels l E Y
    intro n
    apply SheafOfModules.flatOnSite_of_iso (integralCoefficientCommRingSheaf l E Y n)
      ((HomologicalComplex.eval _ _ i).mapIso (κ n)).symm
    exact WeilConjectures.flat_extension l E Y n (P.obj.X i) (P.property.2 i)
  exact (integralComparisonSequenceScalarModel.{u, u} l E L ι X).computes _
    (WeilConjectures.sequencePullback_kflatgood l E f C hk hf)

end WeilConjectures.ScalarExtensionTower
