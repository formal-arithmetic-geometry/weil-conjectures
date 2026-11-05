/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
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
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.Integral.IntegralDerivedPullbackLinear
import WeilConjectures.CategoryTheory.ScalarLocalization.BilinearScalarLocalization

import WeilConjectures.SmoothPurity.Integral.IntegralCompletedTensorBilinear
import WeilConjectures.SmoothPurity.Integral.IntegralDerivedHomBilinear
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationFunctor
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationIso
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationBilinearComparison
import WeilConjectures.SmoothPurity.OperationsScalarLocalization.DerivedScalarLocalizationRestrictedHom

/-! # Finite, integral, and rational derived operations

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1467;
Stacks Project, Tags 06YL, 06YV, 08J7 and 099N
(blueprint: def-sf-finite-rational-derived-operations).

This is the finite, integral, and rational part of
`def-weil-derived-pullback-tensor-hom`, extracted with its declaration names,
signatures, and definitions preserved. The common-stage module re-exports it.

## Main definitions

- `finiteDerivedPullback`: exact intrinsic constant-coefficient inverse image.
- `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`: ambient operations.
- `finiteIntrinsicTensorModels`: K-flat tensor and ordinary evaluation normalization.
- `finiteIntrinsicReductionHom`: reduced evaluation's canonical closed transpose.
- `constructibleIntegralPullback`, `constructibleIntegralTensor`: actual restrictions.
- `constructibleIntegralHom`: ambient Hom restricted to permitted constructible pairs.
- `rationalDerivedPullback`, `rationalDerivedTensor`, `rationalDerivedInternalHom`:
  the uniquely specified linear and bilinear extensions with unchanged integral objects.

The scalar comparisons rationalize the prescribed integral comparisons.
No idempotent completion, arbitrary isomorphism, or extra coefficient flatness is used.
-/

-- The module has public declarations; avoid the costly final private-only style scan.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
-- The generated common-stage types make the section-variable linter expensive.
-- Every retained section parameter is present in the operation's public type.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂

open Opposite TensorProduct

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

-- Keep the chosen derived localization model abstract during elaboration.
attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue

attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralDerivedInternalHom sfRationalScalarExtension
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar

attribute [local irreducible] rationalDerivedPullback

section RationalTensorConstruction
attribute [local irreducible] constructibleIntegralTensor sfIntegralConstructibleLinear
  ObjectProperty.FullSubcategory.category Preadditive.fullSubcategory Linear.fullSubcategory

end RationalTensorConstruction

attribute [local irreducible] rationalDerivedTensor

section RationalHomConstruction
attribute [local irreducible] constructibleIntegralHom sfIntegralConstructibleLinear
  ObjectProperty.FullSubcategory.category Preadditive.fullSubcategory Linear.fullSubcategory

end RationalHomConstruction

section ScalarComparisons
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] rationalDerivedInternalHom

section RationalScalarComparisons
attribute [local irreducible] Linear.homModule Preadditive.homGroup
  ScalarLocalization.linear ScalarLocalization.preadditive sfIntegralConstructibleLinear

attribute [local irreducible] rationalPullbackScalarComparison

end RationalScalarComparisons

attribute [local irreducible] rationalPullbackScalarComparison rationalTensorScalarComparison

end ScalarComparisons

end WeilConjectures
