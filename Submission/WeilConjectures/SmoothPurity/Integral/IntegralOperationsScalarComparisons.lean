/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SmoothPurity.IntegralScalarOperations.IntegralOperationsScalarExtension
public import Submission.WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import Submission.WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels

import Submission.WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralScalarPullbackComparison
import Submission.WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralScalarTensorComparison

import Mathlib.CategoryTheory.Whiskering
import all Submission.WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackTowerRepresentatives
import Submission.WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import Mathlib.CategoryTheory.Limits.HasLimits
import Submission.WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction
import Submission.WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import Submission.WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import Submission.WeilConjectures.SecSmoothPurity.StrictCoefficient.ScalarCalculation.NormalizedScalarTensorTransitionsSupplement
import Submission.WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all Submission.WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import Submission.WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import Submission.WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import Submission.WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import Submission.WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralOrdinaryTensorChain
import Submission.WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarInternalHomComplete
import all Submission.WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all Submission.WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Submission.WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
import Submission.WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeHom
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import Submission.WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Hom
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Submission.WeilConjectures.Algebra.Homology.HomComplex
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import Submission.WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Normalized integral scalar comparisons

The finite-level maps, strict towers, and good-representative models are publicly
re-exported from IntegralOperationsScalarComparisonModels. This file retains the
ordinary derived comparisons, completed comparisons, and coherence statements.
(blueprint: lem-pur-integral-operations-scalar-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
attribute [local irreducible] constantSheaf limit
  integralDerivedPullback integralCompletedTensor integralScalarExtension

/-- The ordinary scalar/pullback comparison is the localization of scalarPullbackChain.
Source: Stacks 07A4, 099N (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the prescribed level generator maps are natural and commute with strict
reductions. The two Roos coordinates therefore give scalarPullbackChain. Finite
freeness commutes with countable products; cofinality of uniformizer filtrations
makes this chain map a quasi-isomorphism on good representatives. Localize the
map, conjugating by the two displayed representative comparisons. Good K-flat
resolutions compute all objects and roofs, giving naturality and invertibility.
The same localization property gives uniqueness with this normalization. -/
theorem scalarPullbackOrdinary_existsUnique {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) :
    ∃! α : integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f,
      scalarPullbackOrdinaryNormalization l E L ι f α := by
  exact normalizedIntegralScalarPullbackComparison l E L ι f

/-- The canonical localized scalar/pullback comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarPullbackOrdinary {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    integralDerivedPullback l E f ⋙ integralOrdinaryDerivedScalar l E L ι X ≅
      integralOrdinaryDerivedScalar l E L ι Y ⋙ integralDerivedPullback l L f :=
  (scalarPullbackOrdinary_existsUnique l E L ι f).exists.choose

/-- The prescribed representative normalization, retained as a named predicate.
Source: Stacks 07A4, 08J9, 08TC
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorOrdinaryNormalization (W : AlgebraicGeometry.Scheme.{u})
    (α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        (integralOrdinaryDerivedScalar l E L ι W).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) ≫
          (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj) =
        α.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (integralCompletedTensor l L W).map
            (CategoryTheory.Prod.mkHom
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P.obj)
              ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (integralCompletedTensorComparison l L W).hom.app
            (⟨_, scalarGood l E L ι W P⟩, ⟨_, scalarGood l E L ι W Q⟩)

/-- The ordinary scalar/completed-tensor comparison has its full Roos normalization.
Source: Stacks 07A4, 099N (blueprint: lem-pur-integral-operations-scalar-extension).
Proof: the finite tensor generator maps respect the signed total differential and
strict reductions. Their diagonal Roos map is scalarTensorChain. Finite freeness
commutes with its products, and the two uniformizer filtrations are cofinal. Thus
this map is a quasi-isomorphism on good pairs. Localize in both variables and
conjugate by the displayed comparisons. Roofs prove naturality and independence;
the universal property of the localization gives uniqueness. -/
theorem scalarTensorOrdinary_existsUnique (W : AlgebraicGeometry.Scheme.{u}) :
    ∃! α : integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W,
      scalarTensorOrdinaryNormalization l E L ι W α := by
  exact normalizedIntegralScalarTensorComparison l E L ι W

/-- The canonical localized scalar/completed-tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarTensorOrdinary (W : AlgebraicGeometry.Scheme.{u}) :
    integralCompletedTensor l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      (integralOrdinaryDerivedScalar l E L ι W).prod
        (integralOrdinaryDerivedScalar l E L ι W) ⋙ integralCompletedTensor l L W :=
  (scalarTensorOrdinary_existsUnique l E L ι W).exists.choose

/-- The intrinsic ordinary closed structure, retaining the recorded ambient Hom.
Source: Stacks 08J9 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarIntegralClosed (W : AlgebraicGeometry.Scheme.{u}) :
    CoefficientClosedStructure (integralDerivedInternalHom l E W) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralClosed

/-- The normalized total tensor models for the same closed structure.
Source: Stacks 07A4 (blueprint: lem-pur-integral-operations-scalar-extension). -/
def scalarIntegralModels (W : AlgebraicGeometry.Scheme.{u}) :
    CoefficientTensorModels.{u, u+1, u, u+2}
      (AlgebraicGeometry.Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) (scalarIntegralClosed l E W) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose.integralTensorModel

attribute [local irreducible] scalarIntegralClosed scalarIntegralModels

section ScalarClosedTensorDescent

end ScalarClosedTensorDescent

section ScalarHomBaseChange

end ScalarHomBaseChange

section ScalarHomCompleteness

/-- Ambient internal Hom into a complete object is complete; constructibility of the
Hom is not assumed. Source: Bhatt--Scholze 3.4.11; Stacks 08JB, 099B
(blueprint: lem-pur-integral-operations-scalar-extension).
Proof: restrict to every slice. Tensor-Hom currying identifies Hom from R[1/t]
into Hom(M,N) with Hom from M into Hom(R[1/t],N), which vanishes by completeness
of N. The local Koszul completion reflector identifies this vanishing with
invertibility of the canonical completion unit. Its Roos triangle is the specified
strict reduction-tower triangle, giving precisely IsSfDerivedComplete. -/
theorem scalarInternalHom_complete (W : AlgebraicGeometry.Scheme.{u})
    (M N : DerivedCategory (integralTowerModules l E W))
    (hN : IsSfDerivedComplete l E W N) :
    IsSfDerivedComplete l E W ((integralDerivedInternalHom l E W).obj (op M, N)) := by
  exact integralScalarInternalHomComplete l E W M N hN

end ScalarHomCompleteness

section ScalarTowerDescent

attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryDerivedScalarComp
attribute [local implicit_reducible] goodScalar
  integralOperationsPullbackOnGood integralOperationsTensorOnGood
  integralOperationsGoodLocalization

attribute [local irreducible] goodScalarComparison

attribute [local irreducible] scalarPullbackOrdinary scalarTensorOrdinary

end ScalarTowerDescent

end WeilConjectures
