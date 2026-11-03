/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeTensor
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeHom
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains

import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Finite.FiniteConstructibleHom
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.SixFunctors.Integral.IntegralConstructibleInternalHom
import WeilConjectures.SixFunctors.Integral.IntegralHomReduction
import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import WeilConjectures.SixFunctors.CompactSupportPbcTransport.CompactSupportProjectionFormula
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientTensorCtf
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.SixFunctors.Supporting.OperationCoefficientActionData
import WeilConjectures.SmoothPurity.Supporting.BasicOperationReductionAndEvaluation
import WeilConjectures.SmoothPurity.Supporting.BasicOperationCoefficientCoherence
import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-!
# Tensor--Hom exchange for the constructible exceptional adjoint

Source: Weil conjectures blueprint, main-20261015, sec-six-functors,
`sk-thm-sf-tensor-hom` (blueprint: sk-thm-sf-tensor-hom).

The exceptional functor is the unconditional constructible adjoint. In particular,
no right adjoint on the entire pro-etale derived category is an input.

## Main definitions

* `RingExchange` records the ambient exchange, boundedness below and signed shifts.
* `CanonicalExchange` fixes the forward map by its projection/counit transpose.
* `Family` records this canonical exchange through all four coefficient regimes.

## Main statements

* `exists_family` supplies this family for the unconditional constructible adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
-- Keep the chosen valuation ring folded while comparing coefficient categories.
attribute [local irreducible] Padic.coefficientExtensionIntegers

universe u v w v₁ w₁
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures
namespace ConstructibleTensorHom
open ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The actual ambient ringed derived category, retaining both small-site universes.
Source: blueprint operations (i)--(ii) (blueprint: sk-thm-sf-tensor-hom). -/
abbrev Ambient (T : Scheme.{u}) (s : RingStage.{u} l) :=
  DerivedCategory (pbcModules T ((s.coefficients l).ring T))

/-- The recorded K-injective internal Hom over the finite or completed ring sheaf.
Source: blueprint operations (i); Stacks 08J7 (blueprint: sk-thm-sf-tensor-hom). -/
abbrev hom (T : Scheme.{u}) (s : RingStage.{u} l) :
    (Ambient l T s)ᵒᵖ × Ambient l T s ⥤ Ambient l T s :=
  CategoryTheory.derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology T) ((s.coefficients l).ring T)

attribute [local irreducible] rationalDerivedPullback sfRationalConstructibleLocalization
  sfRationalScalarExtension rationalDerivedInternalHom

section Family
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

end Family
end ConstructibleTensorHom
end WeilConjectures
