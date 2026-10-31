/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantCoefficientObjectsConstructible
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedSiteDualityMaps
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all WeilConjectures.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus
import all WeilConjectures.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteClopenConstructibilityBounds
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Mathlib.Order.Bounds.Basic
import all WeilConjectures.CategoryTheory.StrictRoosAdditiveComparison
import all WeilConjectures.AlgebraicGeometry.VaryingRingOperations
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso

import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIsoSupplement
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import all WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import all WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.AlgebraicGeometry.FinitePullbackLocalizationCohomology
import WeilConjectures.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection
import all WeilConjectures.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent
import WeilConjectures.AlgebraicGeometry.OpenCompletedRestrictionIdentification
import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

import all WeilConjectures.AlgebraicGeometry.PurityFiniteSetting

/-! # Finite clopen coefficient data and derived support

Source: Stacks Project, Tag 04TS, and the finite-clopen argument in the blueprint
sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: lem-pur-finite-clopen-decomposition-core).

Restrictions below are actual precomposition on the small pro-etale sites. The
coefficient rings are the published finite quotients and completed integral sheaf.
This module contains the original coefficient data and the fully proved support
section extracted from FiniteClopenDerivedDecomposition for compilation time.
-/

@[expose] public noncomputable section
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.monoidal
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.symmetric
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.RingedDerivedNative.monoidal
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

universe u w v c₀ d₀ v₀ z₀ r₀
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
namespace PurityFiniteSetting

private theorem scalarAdditive {C : Type c₀} [Category.{d₀} C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{r₀}} (a : R ⟶ S) :
    (SheafOfModules.restrictScalars.{z₀} a).Additive := inferInstance

private theorem additiveComp {C : Type c₀} {D : Type d₀} {E : Type v₀}
    [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (hF : F.Additive) (hG : G.Additive) :
    (F ⋙ G).Additive := by
  let := hF
  let := hG
  infer_instance

private def pushforwardRestrictIso
    {C : Type c₀} [Category.{d₀} C] {D : Type v₀} [Category.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r₀})
    {S : Sheaf J RingCat.{r₀}}
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{r₀} J K).obj R) :
    SheafOfModules.pushforward.{z₀} (F := F) (𝟙 _) ⋙
        SheafOfModules.restrictScalars a ≅ SheafOfModules.pushforward a :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

variable (P : PurityFiniteSetting.{u})

attribute [-instance] WeilConjectures.OpenCompletedRestriction.globalHasDerived
  SheafOfModules.scalarRestriction_limits SheafOfModules.scalarRestriction_colimits


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Finite or completed coefficients, with n denoting exponent n+1.
Source: Stacks 04TS and the section-invariant finite-clopen argument
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenRing (X : Scheme.{u}) (n : ℕ) (integral : Bool) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  if integral then completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension X
  else integralCoefficientCommRingSheaf P.coefficients.l P.extension X n

attribute [local irreducible] clopenRing

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The actual inclusion of the component site: compose its structure map with j.
Source: Stacks 00XZ, 04TS (blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenSiteInclusion {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Continuity of this concrete site inclusion, with no added assumption.
Source: Stacks 00XZ (blueprint: lem-pur-finite-clopen-decomposition-core). -/
instance clopenSiteInclusionContinuous {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    (clopenSiteInclusion j).IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Restrict a coefficient ring by precomposition along the component site.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenRingRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ((clopenSiteInclusion j).sheafPushforwardContinuous CommRingCat.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj R

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Forget commutativity only; this is the published module-sheaf encoding.
Source: Stacks Modules on Sites (blueprint: lem-pur-finite-clopen-decomposition-core). -/
abbrev clopenModules (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The canonical sectionwise module restriction, including its scalar action.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    clopenModules X R ⥤ clopenModules Y (clopenRingRestriction j R) :=
  SheafOfModules.pushforward (F := clopenSiteInclusion j) (𝟙 _)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Exactness of restriction, required to descend the actual degreewise functor.
Source: Stacks 04TS and 015F (blueprint: lem-pur-finite-clopen-decomposition-core).
Proof: localize the small site at the open immersion (weakly-etale localization).
Restriction of module sheaves is exact; kernels and sheafified cokernels restrict
locally. Its formula is additive. This uses sheaf exactness, not sectionwise
surjectivity of epimorphisms. -/
theorem clopenRestriction_exact {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (clopenRestriction j R).Additive ∧ PreservesFiniteLimits (clopenRestriction j R) ∧
      PreservesFiniteColimits (clopenRestriction j R) := by
  refine ⟨?_, ?_⟩
  · exact Scheme.ProEt.clopenModuleRestriction_additive j _
  · exact Scheme.ProEt.FiniteClopenTensor.restriction_exact.{u, u} j R

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Additivity from exact sectionwise restriction. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
instance clopenRestrictionAdditive {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (clopenRestriction j R).Additive := (clopenRestriction_exact j R).1

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Left exactness from the preceding named theorem. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
instance clopenRestrictionLimits {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (clopenRestriction j R) := (clopenRestriction_exact j R).2.1

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Right exactness from the preceding named theorem. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
instance clopenRestrictionColimits {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (clopenRestriction j R) := (clopenRestriction_exact j R).2.2

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The standard unbounded localization of these abelian module categories.
Source: Stacks 05RU (blueprint: lem-pur-finite-clopen-decomposition-core). -/
instance clopenHasDerived (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory (clopenModules X R) := HasDerivedCategory.standard _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Restrict complexes degreewise and descend through quasi-isomorphisms.
Source: Stacks 015F, 05RU (blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenDerivedRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  (clopenRestriction j R).mapDerivedCategory

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Invertibility of ell in a residue field over the fixed algebraically closed base.
Source: purity conventions (blueprint: lem-pur-finite-clopen-decomposition-core).
Proof: ell differs from p, so is nonzero in k. The structure map to the residue
field carries its inverse in k to an inverse there. No new geometric hypothesis
is required. -/
theorem clopenResidue_isUnit (Y : Over (Spec (CommRingCat.of P.field.k))) (y : Y.left) :
    IsUnit (P.coefficients.l : Y.left.residueField y) := by
  simpa only [map_natCast] using
    (P.coefficientPrime_isUnit_stalk Y.left Y.hom y).map
      (IsLocalRing.residue (Y.left.presheaf.stalk y))

attribute [local irreducible] Scheme.residueField

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The recorded constructible integral pullback, supplying only the source-implied
residue-field invertibility. Source: blueprint integral coefficient conventions
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenIntegralPullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  constructibleIntegralPullback P.coefficients.l P.extension j.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The recorded raw rationalized pullback, without Karoubi completion.
Source: blueprint rational coefficient conventions
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenRationalPullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  rationalDerivedPullback P.coefficients.l P.extension j.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The recorded common-stage pullback, on the fixed algebraic coefficient closure.
Source: blueprint common-stage coefficient conventions
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenCommonStagePullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar j.left


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The completed tensor on the constructible integral category, with the recorded
normalization on strict K-flat towers. Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenIntegralTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  constructibleIntegralTensor P.coefficients.l P.extension Y.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The recorded rational tensor, extended linearly on morphisms.
Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenRationalTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  rationalDerivedTensor P.coefficients.l P.extension Y.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The common-stage tensor, formed at the coefficient compositum.
Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenCommonStageTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar Y.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The actual regular completed module in the intrinsic constructible category.
Only its membership proof comes from the published constant-coefficient theorem.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenIntegralUnit (Y : Scheme.{u}) :
    sfIntegralConstructibleCategory P.coefficients.l P.extension Y :=
  ⟨integralConstantCoefficientObject P.coefficients.l P.extension Y,
    (integralConstantCoefficient_constructible P.coefficients.l P.extension Y
      P.field P.coefficients.different).2.1⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The raw rational image of the same regular integral module.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenRationalUnit (Y : Scheme.{u}) :=
  (sfRationalConstructibleLocalization P.coefficients.l P.extension Y).obj (P.clopenIntegralUnit Y)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The coefficient unit at any finite stage of the fixed algebraic closure.
Its small field model is the published one, and its integral representative is
the regular completed module in degree zero.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenCommonStageUnit (Y : Scheme.{u})
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar) :
    generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar Y :=
  ⟨B, (sfRationalConstructibleLocalization P.coefficients.l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    Y).obj
      ⟨integralConstantCoefficientObject P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B) Y,
        (integralConstantCoefficient_constructible P.coefficients.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
          Y P.field P.coefficients.different).2.1⟩⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The existing canonical integral scalar/restriction comparison, on every finite
coefficient extension including identities. Source: blueprint coefficient transports
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenIntegralScalarComparison (L : Type u) [Field L]
    [Algebra (Padic P.coefficients.l) L] [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (K : sfIntegralConstructibleCategory P.coefficients.l P.extension X.left) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  integralPullbackScalarComparison P.coefficients.l P.extension L ι j.left K

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The same normalized comparison after raw rationalization. Its action is the
linear extension of the preceding integral map, exactly as in the recorded operations.
Source: blueprint coefficient transports
(blueprint: lem-pur-finite-clopen-decomposition-core). -/
def clopenRationalScalarComparison (L : Type u) [Field L]
    [Algebra (Padic P.coefficients.l) L] [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  rationalPullbackScalarComparison P.coefficients.l P.extension L ι j.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private def clopenTowerComplex {A : Type*} [Category A] [HasZeroMorphisms A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X i := C ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i
  d i j :=
    { app := fun n ↦ (C.obj n).d i j
      naturality := fun n m g ↦ (C.map g).comm i j }
  shape i j h := by ext n; exact (C.obj n).shape i j h
  d_comp_d' i j k _ _ := by ext n; exact (C.obj n).d_comp_d i j k

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenRoosIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    Nonempty (integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let G := F.mapHomologicalComplex (.up ℤ)
    let : PreservesLimitsOfShape (Discrete ℕ) G :=
      HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun i ↦ by
        change PreservesLimitsOfShape (Discrete ℕ)
          (HomologicalComplex.eval A (ComplexShape.up ℤ) i ⋙ F)
        infer_instance)
    refine ⟨NatIso.ofComponents (fun C ↦ roosTheta F (clopenTowerComplex C)) ?_⟩
    intro C D a
    let f : clopenTowerComplex C ⟶ clopenTowerComplex D :=
      { f := fun i ↦
          { app := fun n ↦ (a.app n).f i
            naturality := fun n m g ↦ congrArg (fun z ↦ z.f i) (a.naturality g) }
        comm' := fun i j _ ↦ by ext n; exact (a.app n).comm i j }
    exact roosTheta_map F _ _ (strictRoosProductMap_comm f)
      _ _ (strictRoosProductMap_comm
        ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).map f))
      (roosComparison_map F f) (roosComparison_map F f)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenSupport_iso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory Y A} (e : K ≅ L) :
    Scheme.proEtaleCohomologicalSupport K = Scheme.proEtaleCohomologicalSupport L := by
  ext m
  exact not_congr ⟨fun h ↦ h.of_iso ((DerivedCategory.homologyFunctor _ m).mapIso e).symm,
    fun h ↦ h.of_iso ((DerivedCategory.homologyFunctor _ m).mapIso e)⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenTor_iso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ) :
    Scheme.HasProEtaleTorAmplitude Y A K a b ↔
      Scheme.HasProEtaleTorAmplitude Y A L a b := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro T Q ht f hf hQ M q hq
    exact h.2 T Q ⟨ht.some ≪≫ e.symm⟩ f hf hQ M q hq
  · intro h
    refine ⟨h.1, ?_⟩
    intro T Q ht f hf hQ M q hq
    exact h.2 T Q ⟨ht.some ≪≫ e⟩ f hf hQ M q hq

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenSheafConstructible_iso {Y : Scheme.{u}} {A : Type u}
    [CommRing A] [Finite A]
    {F G : Scheme.proEtaleRingModules Y (Scheme.proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : Scheme.IsConstructibleProEtaleModuleSheaf Y A F) :
    Scheme.IsConstructibleProEtaleModuleSheaf Y A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' := (Scheme.proEtaleConstantRingPullback A (S.immersion i)).mapIso e
  obtain ⟨I, U, f, hc, ht⟩ := (hS i).1
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨M, ⟨hM⟩⟩ := ht j
    exact ⟨M, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso e'.symm ≪≫ hM⟩⟩
  · intro Ω _ _ y
    let E := Scheme.geometricRingModuleStalkFunctor y (Scheme.proEtaleConstantRing (S.domain i) A)
    have : Finite (E.obj ((Scheme.proEtaleConstantRingPullback A
        (S.immersion i)).obj F)) := (hS i).2 Ω y
    exact Finite.of_injective (E.mapIso e'.symm).toLinearEquiv
      (E.mapIso e'.symm).toLinearEquiv.injective

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenTor_mono {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K : Scheme.proEtaleDerivedCategory Y A} {a b c d : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude Y A K a b) (hca : c ≤ a) (hbd : b ≤ d) :
    Scheme.HasProEtaleTorAmplitude Y A K c d := by
  refine ⟨hca.trans (h.1.trans hbd), ?_⟩
  intro L Q e f hf hQ M q hq
  exact h.2 L Q e f hf hQ M q (hq.imp (fun h ↦ h.trans_le hca)
    (fun h ↦ hbd.trans_lt h))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def compareLocalizedBifunctors {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (L : A ⥤ B) (W : MorphismProperty A)
    [(L.prod L).IsLocalization (W.prod W)]
    (F G : B × B ⥤ C) (α : (L.prod L) ⋙ F ≅ (L.prod L) ⋙ G) : F ≅ G :=
  (Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W) C).preimageIso α

private theorem clopenTensorModelIso (Y : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (M : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology Y) R) :
    Nonempty (M.closed.tensor ≅
      @MonoidalCategory.tensor (DerivedCategory (clopenModules Y R)) _
        (Scheme.ProEt.FiniteClopenTensor.derivedMonoidal.{u, u} R)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let L := coefficientKFlatInclusion.{u, u + 1, u} (Scheme.ProEt.topology Y) R ⋙
      DerivedCategory.Q
    let W := (HomologicalComplex.quasiIso (clopenModules Y R) (.up ℤ)).inverseImage
      (coefficientKFlatInclusion.{u, u + 1, u} (Scheme.ProEt.topology Y) R)
    let : L.IsLocalization W :=
      RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2}
        (Scheme.ProEt.topology Y) R
    exact ⟨compareLocalizedBifunctors L W M.closed.tensor
      (@MonoidalCategory.tensor (DerivedCategory (clopenModules Y R)) _
        (Scheme.ProEt.FiniteClopenTensor.derivedMonoidal.{u, u} R))
      (M.models.comparison.symm ≪≫
        RingedDerivedNative.comparison.{u + 1, u, u, u + 2} (Scheme.ProEt.topology Y) R)⟩


private def scalarSquare {A B C D E : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (H : A ⥤ B) (F : B ⥤ C) (G : D ⥤ E)
    (S S' : B ⥤ D) (T T' : C ⥤ E)
    (α : H ⋙ S ≅ H ⋙ S') (β : F ⋙ T ≅ S ⋙ G)
    (γ : (H ⋙ F) ⋙ T ≅ (H ⋙ F) ⋙ T') : H ⋙ S' ⋙ G ≅ (H ⋙ F) ⋙ T' :=
  (Functor.associator H S' G).symm ≪≫ isoWhiskerRight α.symm G ≪≫
    Functor.associator H S G ≪≫ isoWhiskerLeft H β.symm ≪≫
    (Functor.associator H F T).symm ≪≫ γ


private def pushUnitThroughIso
    {C : Type c₀} [Category.{v₀} C] {D : Type d₀} [Category.{z₀} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r₀})
    {S : Sheaf J RingCat.{r₀}}
    (e : S ≅ (F.sheafPushforwardContinuous RingCat.{r₀} J K).obj R) :
    (SheafOfModules.pushforward.{r₀} (F := F) e.hom).obj
      (SheafOfModules.unit R) ≅ SheafOfModules.unit S := by
  let f : SheafOfModules.unit S ⟶
      (SheafOfModules.pushforward.{r₀} (F := F) e.hom).obj (SheafOfModules.unit R) :=
    SheafOfModules.unitToPushforwardObjUnit e.hom
  have h (U : Cᵒᵖ) : IsIso (f.val.app U) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ConcreteCategory.bijective_of_isIso (e.hom.hom.app U)
  let t := PresheafOfModules.isoMk (fun U ↦ @asIso _ _ _ _ (f.val.app U) (h U))
    (by intro U V g; exact f.val.naturality g)
  exact ((SheafOfModules.fullyFaithfulForget S).preimageIso
    (X := SheafOfModules.unit S)
    (Y := (SheafOfModules.pushforward.{r₀} (F := F) e.hom).obj (SheafOfModules.unit R)) t).symm

private theorem rationalPullback_formula (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ x : X, Invertible (l : X.residueField x)] :
    (∀ K, (rationalDerivedPullback l E f).obj K =
      ⟨(constructibleIntegralPullback l E f).obj K.obj⟩) ∧
    (∀ (K M : sfIntegralConstructibleCategory l E X) (a : K ⟶ M)
      (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
      HEq ((rationalDerivedPullback l E f).map
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a :
          (sfRationalConstructibleLocalization l E X).obj K ⟶
          (sfRationalConstructibleLocalization l E X).obj M))
        (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          (constructibleIntegralPullback l E f).map a)) := by
  unfold rationalDerivedPullback
  exact (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2


private def pullbackInclusion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ x : X, Invertible (l : X.residueField x)] :
    (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E f ≅
      constructibleIntegralPullback l E f ⋙ (sfIntegralConstructible l E Y).ι := by
  unfold constructibleIntegralPullback
  exact Iso.refl _

private def transportTensorComparison {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (T T' : A × A ⥤ A) (S S' : B × B ⥤ B)
    (a : T ≅ T') (b : S ≅ S') (c : T' ⋙ F ≅ F.prod F ⋙ S') :
    T ⋙ F ≅ F.prod F ⋙ S :=
  isoWhiskerRight a F ≪≫ c ≪≫ isoWhiskerLeft (F.prod F) b.symm

section GenericDecomposition
variable (X : Over (Spec (CommRingCat.of P.field.k)))
  {I : Type w} [Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left) (Set.range (j k).left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)
include hdisjoint hcover
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
private theorem unboundedForRing
    (R : Sheaf (Scheme.ProEt.topology X.left) CommRingCat.{u + 1}) :
    (Functor.pi' (fun i ↦
      clopenDerivedRestriction (j i).left R)).IsEquivalence ∧
    (∀ (i : I) (m : ℤ), Nonempty
      (clopenDerivedRestriction (j i).left R ⋙
          DerivedCategory.homologyFunctor _ m ≅
        DerivedCategory.homologyFunctor _ m ⋙
          clopenRestriction (j i).left R)) ∧
    (∀ i : I, Nonempty
      ((clopenDerivedRestriction (j i).left R).obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              R))) ≅
        (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (clopenRingRestriction (j i).left R))))) ∧
    ∀ (M : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology X.left)
        R) (i : I)
      (Mi : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology (Xi i).left)
        (clopenRingRestriction (j i).left R)),
      Nonempty (M.closed.tensor ⋙
          clopenDerivedRestriction (j i).left R ≅
        ((clopenDerivedRestriction (j i).left R).prod
          (clopenDerivedRestriction (j i).left R)) ⋙
            Mi.closed.tensor) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    have hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i).left) (Set.range (j k).left)) :=
      hdisjoint
    have hc : ∀ x : X.left, ∃ i, x ∈ Set.range (j i).left := by
      intro x
      have hx : x ∈ ⋃ i, Set.range (j i).left := by rw [hcover]; trivial
      exact Set.mem_iUnion.mp hx
    have H :=
      Scheme.ProEt.FiniteClopenTensor.finite_clopen_derived_calculus.{u, u, w, 0, 0}
        X.left I (fun i ↦ (Xi i).left) (fun i ↦ (j i).left) hd hc R
    have ht := Scheme.ProEt.ClopenMonoidalDescent.clopen_kflat_monoidal_descent.{u, u, w}
      X.left I (fun i ↦ (Xi i).left) (fun i ↦ (j i).left) hd hc R
    refine ⟨?_, ?_, ?_, ?_⟩
    · let e := H.choose
      have he := H.choose_spec.1
      change (Functor.pi' (fun i ↦
        Scheme.ProEt.FiniteClopenTensor.derivedRestriction.{u, u} (j i).left R)).IsEquivalence
      rw [← he]
      infer_instance
    · intro i m
      exact ⟨((clopenRestriction (j i).left R).mapDerivedCategoryHomologyFunctorIso m).symm⟩
    · intro i
      exact ⟨((clopenRestriction (j i).left R).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (Iso.refl _)⟩
    · intro M i Mi
      let c := (ht.2.choose_spec i).choose_spec.choose_spec.choose
      exact ⟨transportTensorComparison (clopenDerivedRestriction (j i).left R)
        M.closed.tensor _ Mi.closed.tensor _
        (clopenTensorModelIso X.left R M).some
        (clopenTensorModelIso (Xi i).left (clopenRingRestriction (j i).left R) Mi).some
        c⟩


end GenericDecomposition

section UnitHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (X : Over (Spec (CommRingCat.of P.field.k)))
variable {I : Type w} (Xi : I → Over (Spec (CommRingCat.of P.field.k)))
variable (j : ∀ i, Xi i ⟶ X)
variable [∀ i, IsOpenImmersion (j i).left]
private theorem integralUnitCheck
    (E : Type u) [Field E] [Algebra ℚ_[P.coefficients.l] E]
    [FiniteDimensional ℚ_[P.coefficients.l] E]
    [∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x)]
    [∀ k (x : (Xi k).left), Invertible (P.coefficients.l : (Xi k).left.residueField x)]
    (i : I) :
    Nonempty ((integralDerivedPullback P.coefficients.l E (j i).left).obj
      (integralConstantCoefficientObject P.coefficients.l E X.left) ≅
        integralConstantCoefficientObject P.coefficients.l E (Xi i).left) := by
  let l := P.coefficients.l
  let R := completedIntegralCommRingSheafUnrestricted l E X.left
  let S := completedIntegralCommRingSheafUnrestricted l E (Xi i).left
  let V := sheafCompose (Scheme.ProEt.topology (Xi i).left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let e := V.mapIso (OpenCompletedRestriction.coefficients.{u, u} l E (j i).left).completed
  let v := pushUnitThroughIso.{u + 1, u + 1, u, u, u + 1}
    (OpenCompletedRestriction.inclusion (j i).left)
    ((sheafCompose (Scheme.ProEt.topology X.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) e
  obtain ⟨d, hd⟩ := OpenCompletedRestriction.open_completed_restriction_complete
    l E (j i).left inferInstance inferInstance
  let K := integralConstantCoefficientObject l E X.left
  let F : scalarReductionSource l E X.left ⥤ scalarReductionSource l E (Xi i).left :=
    OpenCompletedRestriction.ordinary.{u, u} l E (j i).left
  let hAdd : F.Additive := OpenCompletedRestriction.ordinaryAdditive.{u, u} l E (j i).left
  let hLim : CategoryTheory.Limits.PreservesFiniteLimits F :=
    OpenCompletedRestriction.ordinaryLimits.{u, u} l E (j i).left
  let hCol : CategoryTheory.Limits.PreservesFiniteColimits F :=
    OpenCompletedRestriction.ordinaryColimits.{u, u} l E (j i).left
  let h : IsIso ((OpenCompletedRestriction.kappa.{u, u} l E (j i).left d).app K) :=
    hd K (integralConstantCoefficient_constructible l E X.left P.field
      P.coefficients.different).2.1
  exact ⟨(@asIso _ _ _ _ ((OpenCompletedRestriction.kappa.{u, u} l E (j i).left d).app K) h).symm ≪≫
    (@Functor.mapDerivedCategorySingleFunctor _ _ _ _ _ _ _ _ F
      hAdd hLim hCol 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso v⟩

private theorem finiteUnitCheck (n : ℕ) (i : I) :
    Nonempty ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj
      (finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) ≅
        finiteConstantCoefficientObject P.coefficients.l P.extension (Xi i).left n) := by
  let := fun y : (Xi i).left ↦ (P.clopenResidue_isUnit (Xi i) y).invertible
  let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  let U : X.left.ProEt := ⟨Over.mk (j i).left, show WeaklyEtale (j i).left from inferInstance⟩
  let d := (Scheme.finite_pullback_localization_cohomology P.coefficients.l
    P.extension n X.left U).some
  let A := Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)
  let V := sheafCompose (Scheme.ProEt.topology (Xi i).left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let e := V.mapIso d.ringIso
  let v := pushUnitThroughIso.{u + 1, u + 1, u, u, u + 1} (clopenSiteInclusion (j i).left)
    ((sheafCompose (Scheme.ProEt.topology X.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Scheme.proEtaleConstantRing X.left A)) e
  let F := Scheme.proEtaleObjectModuleRestriction U A d.ringIso
  let hAdd := d.restrictionAdditive
  let hLim := d.restrictionLimits
  let hCol := d.restrictionColimits
  exact ⟨d.derivedComparison.app _ ≪≫
    (@Functor.mapDerivedCategorySingleFunctor _ _ _ _ _ _ _ _ F
      hAdd hLim hCol 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso v⟩
private theorem rationalUnitCheck (E : Type u) [Field E]
    [Algebra ℚ_[P.coefficients.l] E] [FiniteDimensional ℚ_[P.coefficients.l] E]
    [∀ x : X.left, Invertible (P.coefficients.l : X.left.residueField x)]
    [∀ k (x : (Xi k).left), Invertible (P.coefficients.l : (Xi k).left.residueField x)]
    (i : I) (K : sfIntegralConstructibleCategory P.coefficients.l E X.left)
    (Ki : sfIntegralConstructibleCategory P.coefficients.l E (Xi i).left)
    (hK : K.obj = integralConstantCoefficientObject P.coefficients.l E X.left)
    (hKi : Ki.obj = integralConstantCoefficientObject P.coefficients.l E (Xi i).left) :
    Nonempty ((rationalDerivedPullback P.coefficients.l E (j i).left).obj
      ((sfRationalConstructibleLocalization P.coefficients.l E X.left).obj K) ≅
        (sfRationalConstructibleLocalization P.coefficients.l E (Xi i).left).obj Ki) := by
  let l := P.coefficients.l
  obtain ⟨v⟩ := integralUnitCheck P X Xi j E i
  let vi : (constructibleIntegralPullback l E (j i).left).obj K ≅ Ki :=
    ObjectProperty.isoMk _ ((integralDerivedPullback l E (j i).left).mapIso
      (eqToIso hK) ≪≫ v ≪≫ (eqToIso hKi).symm)
  exact ⟨eqToIso ((rationalPullback_formula l E (j i).left).1
    ((sfRationalConstructibleLocalization l E X.left).obj K)) ≪≫
    (sfRationalConstructibleLocalization l E (Xi i).left).mapIso vi⟩

private theorem commonStagePullback_obj (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {W V : Scheme.{u}} (f : W ⟶ V)
    [∀ x : W, Invertible (l : W.residueField x)]
    [∀ y : V, Invertible (l : V.residueField y)]
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω V) :
    (commonStageDerivedPullback l Ω f).obj A = commonStagePullbackObject l Ω f A := by
  dsimp only [commonStageDerivedPullback]
  exact (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 A

attribute [local irreducible] commonStageDerivedPullback in
attribute [local irreducible] ScalarLocalization.category
  ObjectProperty.FullSubcategory.category in
private theorem commonUnitCheck (i : I)
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar) :
    Nonempty ((P.clopenCommonStagePullback (j i)).obj (P.clopenCommonStageUnit X.left B) ≅
      P.clopenCommonStageUnit (Xi i).left B) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
    let := fun k (x : (Xi k).left) ↦ (P.clopenResidue_isUnit (Xi k) x).invertible
    let E := AlgebraicallyClosedCoefficients.Coefficient.{u}
      P.coefficients.l P.coefficients.Qbar B
    let K : sfIntegralConstructibleCategory P.coefficients.l E X.left :=
      ⟨integralConstantCoefficientObject P.coefficients.l E X.left,
        (integralConstantCoefficient_constructible P.coefficients.l E X.left
          P.field P.coefficients.different).2.1⟩
    let Ki : sfIntegralConstructibleCategory P.coefficients.l E (Xi i).left :=
      ⟨integralConstantCoefficientObject P.coefficients.l E (Xi i).left,
        (integralConstantCoefficient_constructible P.coefficients.l E (Xi i).left
          P.field P.coefficients.different).2.1⟩
    obtain ⟨v⟩ := rationalUnitCheck P X Xi j E i K Ki rfl rfl
    let M := P.clopenCommonStageUnit X.left B
    have hM := commonStagePullback_obj P.coefficients.l
      P.coefficients.Qbar (j i).left M
    let e := (GeneralAlgebraicallyClosedCoefficients.inclusion B).mapIso v
    refine ⟨eqToIso hM ≪≫ ?_⟩
    exact e
end UnitHelpers

end PurityFiniteSetting
end WeilConjectures
