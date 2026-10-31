/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdPullbackComparison
public import WeilConjectures.SixFunctors.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.TraceFormula.CounitRealization.CounitRealizationSubstitution
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.TraceFormula.Supporting.EffectiveComparisonRealizationModels
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.ProperBaseChange.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Matching pullback augmentations and entire-tower counits

Source: blueprint main-20261015, sec-fourier-transform/sk-def-trace,
`def-fd-trace-function.md`, final sentence; Stacks Tags 099N(2),(5) and 0941
(blueprint: lem-fd-pullback-augmentation-counit-matching).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The finite quotient augmentation read from the actual zero-shifted chain map.
Source: Stacks 099N(5), 0941; trace-definition final sentence
(blueprint: lem-fd-pullback-augmentation-counit-matching). -/
def fdPullbackQuotientAugmentation (E : Padic.FiniteCoefficientFields l Ω)
    {U T : Scheme.{u}} {h : U ⟶ T} (c : FdPullbackChain l Ω E h)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ)
    (n : ℕ) :=
  c.map.app P ≫
    ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) U).mapHomologicalComplex
      (.up ℤ)).map
      (CochainComplex.mappingCocone.fst (fdPullbackEndomorphism l Ω E h P) ≫
        Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l
          (pbcFiniteField.{u} l Ω E) h).obj P).obj (op m)) n)

/-- The ordinary-limit presentation of the actual whole-tower counit on a resolution.
Source: Stacks 0941; trace-definition final sentence
(blueprint: lem-fd-pullback-augmentation-counit-matching). -/
def FdEntireTowerCounitFormula (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (U : Scheme.{u}) : Prop :=
  ∀ (C I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E U) ℤ)
    (q : C ⟶ I) [QuasiIso q] [I.IsKInjective]
    (_hi : ∀ i : ℤ, Injective (I.X i)),
    (integralComparisonTowerCounit l E U).app (DerivedCategory.Q.obj C) =
      (integralComparisonConstantTower l E U).map
        ((coefficientConstantTowerLimit l E U).map (DerivedCategory.Q.map q)) ≫
      (integralComparisonConstantTower l E U).map
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E U) ⥤ scalarReductionSource l E U) I).hom ≫
      (Functor.const ℕᵒᵖ : scalarReductionSource l E U ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E U).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E U) ⥤
            scalarReductionSource l E U).mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E U)).counit (.up ℤ)).app I) ≫
      inv (DerivedCategory.Q.map q)

/-- The same normalized Roos model computes rho by H(q) followed by inverse iota.
Source: Stacks 0941; trace-definition final sentence
(blueprint: lem-fd-pullback-augmentation-counit-matching). -/
def FdRoosResolutionFormula (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (U : Scheme.{u})
    (r : IntegralComparisonRoosModel l E U) : Prop :=
  ∀ (C I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E U) ℤ)
    (q : C ⟶ I) [QuasiIso q] [I.IsKInjective]
    (_hi : ∀ i : ℤ, Injective (I.X i)),
    ∃ εI : DerivedCategory.Q.obj
        (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E U) ⥤
          scalarReductionSource l E U).mapHomologicalComplex (.up ℤ)).obj I) ≅
        DerivedCategory.Q.obj (integralOperationsRoos I.asFunctor),
      εI.hom = DerivedCategory.Q.map (integralComparisonLimitToRoos l E U I) ∧
      r.comparison.inv.app C =
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q)) ≫
        εI.inv ≫
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E U) ⥤ scalarReductionSource l E U) I).inv ≫
        inv ((coefficientConstantTowerLimit l E U).map (DerivedCategory.Q.map q))

/-- Derived change of rings takes epsilon to the actual quotient-system counit.
Source: Stacks 0941 and 06YY; trace-definition final sentence
(blueprint: lem-fd-pullback-augmentation-counit-matching). -/
def FdReductionCounitFormula (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (U : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E U) : Prop :=
  ∀ N : coefficientSequenceDerived l E U,
    S.adjunction.counit.app N =
      (integralComparisonReductionFactor l E U S).inv.app
        ((coefficientSequenceLimit l E U).obj N) ≫
      (integralComparisonSystemExtension l E U).map
        ((integralComparisonTowerCounit l E U).app
          ((coefficientSequenceDerivedRestriction l E U).obj N)) ≫
      (Adjunction.ofIsRightAdjoint
        (coefficientSequenceDerivedRestriction l E U)).counit.app N

/-- Use one realization system at every location and every letter of a finite word.
Source: Stacks 0941; trace-definition final sentence
(blueprint: lem-fd-pullback-augmentation-counit-matching). -/
def fdCounitRealizationModels (D : IntegralComparisonSystem.{u} l) :
    CounitRealization.Models.{u} l where
  system a := (D.coefficient a.coefficient.carrier).system a.scheme
  roos a := (D.coefficient a.coefficient.carrier).roos a.scheme
  pullback E _X _Y _hX _hY f := (D.coefficient E.carrier).pullback f
  scalar E L ι X := (D.scalar E.carrier L.carrier ι).model X

/-- Match the ambient comparison with the prescribed total-limit realization.
The realization identification is fixed by its actual completion augmentation.
Every comparison with a tower presentation is an isomorphism of entire strict towers.
Source: Stacks 099N(2),(5), 0941; trace-definition final sentence
(blueprint: lem-fd-pullback-augmentation-counit-matching). -/
def FdPullbackRoosMatching
    {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω)
    (D : IntegralComparisonSystem.{u} l) (d : FdPullbackComparison l Ω CU CT h E) : Prop :=
  ∃ b : integralDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom ⋙
      integralDetailedTransport U l (pbcFiniteField.{u} l Ω E) ≅
    integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
      pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω E),
    (∀ K, HEq (b.inv.app K.obj) (d.ambient.hom.app K)) ∧
    (∀ (P : (integralOperationsGoodComplex l
        (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
      (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l
        (pbcFiniteField.{u} l Ω E) U) ℤ)
      (e : C.asFunctor ≅ (integralOperationsPullbackTowerFunctor l
        (pbcFiniteField.{u} l Ω E) h.hom).obj P.obj),
      ∃ j : (pbcActualCompletedPull h.hom (pbcStageDatum.{u} l Ω E)).obj
          ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj
            (DerivedCategory.Q.obj P.obj)) ≅
        (integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).obj
          ((coefficientConstantTowerLimit l (pbcFiniteField.{u} l Ω E) U).obj
            (DerivedCategory.Q.obj C)),
        b.hom.app (DerivedCategory.Q.obj P.obj) ≫ j.hom =
          (integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).map
            ((integralDerivedPullbackComparison l
                (pbcFiniteField.{u} l Ω E) h.hom).hom.app P ≫
              DerivedCategory.Q.map (integralOperationsRoosFunctor.map e.inv) ≫
              ((D.coefficient (pbcFiniteField.{u} l Ω E)).roos U).comparison.inv.app C) ∧
        (pbcActualCompletedPullUnit h.hom (pbcStageDatum.{u} l Ω E)).app
            ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj
              (DerivedCategory.Q.obj P.obj)) ≫ j.hom =
          (pbcActualDerivedPull h.hom (pbcStageDatum.{u} l Ω E)).map
              ((fdCoefficientTransportFactors l
                (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
            pbcActualPullComplexCounit h.hom (pbcStageDatum.{u} l Ω E)
              (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
                 (.up ℤ)).obj P.obj) ≫
            DerivedCategory.Q.map (d.chain.map.app P.obj) ≫
            (fdCoefficientTransportFactors l
              (pbcFiniteField.{u} l Ω E) U).inv.app
                ((integralOperationsPullbackComplexFunctor l
                  (pbcFiniteField.{u} l Ω E) h.hom).obj P.obj) ≫
            (integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).map
              (DerivedCategory.Q.map (integralOperationsRoosFunctor.map e.inv) ≫
                ((D.coefficient (pbcFiniteField.{u} l Ω E)).roos U).comparison.inv.app C))

/-- Quotient augmentations, their actual zero-shifted chain map, normalized Roos
comparison, and the entire-system counit can be matched simultaneously.
Source: blueprint main-20261015, def-fd-trace-function, final sentence;
Stacks 099N(2),(5), 0941
(blueprint: lem-fd-pullback-augmentation-counit-matching).

Proof: (1) The common strict tower models identify both completed pullbacks with
one quotient tower and the coefficient identity normalized by all projections.
(2) On inverse-image unit generators reduction and finite inverse image send p to
(p tensor 1) tensor 1. Quotient transitions preserve 1, giving compatibility.
The tuple is killed by 1-s, so (0,tuple) is a natural chain map; its shifted
coordinate is identically zero, as recorded by FdPullbackChain.
(3) Exact countable products and strictRoosComparison identify H(Q) with Rlim Q.
For a resolution q, H(q)Gamma equals iota times the ordinary-limit lift of q gamma.
The normalized comparison therefore carries Gamma to the actual augmentation,
including the ordinary derived-pullback counit and localization factors.
(4) Invert the ambient comparison and restrict to the full constructible categories.
Raw localization maps each component and its inverse to its tensor with 1.
This gives FdPullbackComparison, with its original normalization equation.
(5) The constant-tower/limit counit on a K-injective resolution is the ordinary
limit cone followed by the inverse of q. Transport through rho cancels the two
adjacent inverse factors in the derived category of entire towers. Derived
change of rings then gives integralComparisonReductionCounit_formula.
(6) effectiveComparisonRealizationModels supplies one system for all finite fields
and maps, with these same normalized primitive models and initial augmentation.
(7) counitRealizationSubstitution applies to that single system. Its empty word
is identity and its cut formula retains the actual intermediate counit under
composition, whiskering and inversion. Its scalar laws include identity and
composite coefficient inclusions. No assertion is inferred from separate finite
reductions and no quotient K-flatness or finite Tor-amplitude is assumed. -/
theorem fdPullbackAugmentationCounitMatching :
    ∃ D : IntegralComparisonSystem.{u} l,
      (CounitRealization.WordLaws (fdCounitRealizationModels l D) ∧
        CounitRealization.ScalarLaws (fdCounitRealizationModels l D)) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
        [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
        [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
        IntegralComparisonRealizationCoherence l E L ι D) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
        [FiniteDimensional ℚ_[l] E] (U : Scheme.{u}) [IsNoetherian U]
        [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
        [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))],
        FdRoosResolutionFormula l E U ((D.coefficient E).roos U) ∧
          FdEntireTowerCounitFormula l E U ∧
          FdReductionCounitFormula l E U ((D.coefficient E).system U)) ∧
      (∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
        [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
        [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
        [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
        [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
        (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
        (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
        ∃ d : FdPullbackComparison l Ω CU CT h E,
          FdPullbackRoosMatching l Ω CU CT h E D d ∧
          ∀ (P : CochainComplex
            (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) (n : ℕ),
            fdPullbackQuotientAugmentation l Ω E d.chain P (n + 1) ≫
              ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) U).mapHomologicalComplex
                 (.up ℤ)).map
                (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l
                  (pbcFiniteField.{u} l Ω E) h.hom).obj P) n) =
              fdPullbackQuotientAugmentation l Ω E d.chain P n) := by
  sorry

end WeilConjectures
