/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
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
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
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
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDecompositionCore

import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDecompositionCore
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData

/-! # Finite clopen decomposition of derived coefficient categories

Source: Stacks Project, Tag 04TS, and the finite-clopen argument in the blueprint
sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: lem-pur-finite-clopen-derived-decomposition).

Restrictions below are actual precomposition on the small pro-etale sites. The
coefficient rings are the published finite quotients and completed integral sheaf.
-/

@[expose] public noncomputable section
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.hasDerived
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.monoidal
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.symmetric
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
-- Preserve the fixed coefficient universes after importing the private support API.
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenScalar.derived
  AlgebraicGeometry.Scheme.ProEt.ClopenScalar.sheafify
  AlgebraicGeometry.Scheme.ProEt.ClopenScalar.locallyBijective
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.sheafify
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.locallyBijective
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.RingedDerivedNative.monoidal
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

universe u w v c₀ d₀ v₀ z₀ r₀
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

attribute [-instance] WeilConjectures.OpenCompletedRestriction.globalHasDerived
  SheafOfModules.scalarRestriction_limits SheafOfModules.scalarRestriction_colimits

attribute [local irreducible] clopenRing Scheme.residueField

section Decomposition
variable (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hft hqc hfinite hclosed hdisjoint hcover

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [local irreducible] rationalDerivedPullback constructibleIntegralPullback
  integralDerivedPullback
  integralScalarExtension

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
set_option allowUnsafeReducibility true
attribute [local reducible] clopenRing

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
end Decomposition
end PurityFiniteSetting
end WeilConjectures
