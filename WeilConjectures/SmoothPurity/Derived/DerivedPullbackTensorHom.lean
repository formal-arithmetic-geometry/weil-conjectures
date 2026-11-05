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
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData
public import WeilConjectures.SmoothPurity.Common.CommonStagePullbackData
public import WeilConjectures.SmoothPurity.Common.CommonStagePullbackDescent
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

import WeilConjectures.SmoothPurity.CommonStageInternalHomDescent.CommonStageInternalHomDescent
import WeilConjectures.SmoothPurity.NormalizedPairDescent.PairDescentPrescribedComponents
import WeilConjectures.SmoothPurity.RawBilinearScalarComparison.RawBilinearScalarComparison
import all WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! # Derived pullback, tensor product, and internal Hom

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1467;
Stacks Project, Tags 06YL, 06YV, 08J7 and 099N
(blueprint: def-weil-derived-pullback-tensor-hom).

The ambient operations for every commutative condensed coefficient ring are the
existing module-object derived pullback, K-flat relative tensor and closed internal Hom,
publicly re-exported here. `ambientDerivedOperations_spec` records their defining
properties and the exact termwise pullback comparison.

The finite, integral, rational and common-stage declarations below retain the legacy
constructible interfaces for their existing consumers. They do not define the ambient
operations of the current blueprint.

## Main definitions

- `finiteDerivedPullback`: exact intrinsic constant-coefficient inverse image.
- `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`: ambient operations.
- `finiteIntrinsicTensorModels`: K-flat tensor and ordinary evaluation normalization.
- `finiteIntrinsicReductionHom`: reduced evaluation's canonical closed transpose.
- `constructibleIntegralPullback`, `constructibleIntegralTensor`: actual restrictions.
- `constructibleIntegralHom`: ambient Hom restricted to permitted constructible pairs.
- `rationalDerivedPullback`, `rationalDerivedTensor`, `rationalDerivedInternalHom`:
  the uniquely specified linear and bilinear extensions with unchanged integral objects.
- `commonStageDerivedPullback`, `commonStageDerivedTensor`, `commonStageDerivedInternalHom`:
  operations on the recorded pair category, with normalized representative formulas.

Every common-stage comparison rationalizes the prescribed integral comparison.
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

section PairDescent
variable {I : Type*} [Preorder I] [IsDirectedOrder I]
  {C : I → Type*} [∀ i, Category* (C i)]
  {D : I → Type*} [∀ i, Category* (D i)]
  (S : StageSystem C) (T : StageSystem D) (φ : ∀ i, C i ⥤ D i)

end PairDescent

/-! Private helpers of the former single module, kept here verbatim: the importers
`FiniteProductFieldCoefficientDescent` and `RationalRestrictionComparisonCoherence` use them
through `import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom`. -/

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue

attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralDerivedInternalHom sfRationalScalarExtension
  completedIntegralCoefficientSheafUnrestricted integralScalarExtension integralOrdinaryScalar

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor

section CommonStage
attribute [local irreducible] rationalDerivedInternalHom
  ScalarLocalization.composition StageSystem.PairCategory.mkHom
attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

attribute [local irreducible] rationalHomScalarComparison
  sfConstructibleIntegralScalarExtension sfIntegralScalarComp sfIntegralScalarUnit

attribute [local irreducible] operationStageTransitionIso

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

attribute [local irreducible] commonStagePullbackComparison

section PullbackProofs

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local irreducible] ScalarLocalization.category

end PullbackProofs

section ComparisonElaboration
attribute [local irreducible] ObjectProperty.FullSubcategory.category

end ComparisonElaboration

attribute [local irreducible] commonStageTensorComparison

section TensorDescentElaboration
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.pairCategory CategoryTheory.uniformProd
attribute [local semireducible] operationStageTransitionIso
attribute [local irreducible] ObjectProperty.FullSubcategory.category ScalarLocalization.category

end TensorDescentElaboration

section HomDescent

attribute [local irreducible] commonStageHomComparison
set_option allowUnsafeReducibility true in
attribute [local reducible] commonStageHomObject commonStageHomPairAtStage
  GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.pairCategory
attribute [local irreducible] ScalarLocalization.category
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local implicit_reducible] catToReflQuiver

open CommonStageInternalHom CommonStageInternalHomDescent

end HomDescent

end CommonStage
end WeilConjectures

open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxSize 2048

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

end AlgebraicGeometry.ProEtale.CondensedRing
