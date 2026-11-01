/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteDualizing
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteModuleEquivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.AlgebraicGeometry.ScalarUnitRestrictionSingle
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageBalancingCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Compact.CompactCoefficientComposition
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.SixFunctors.Supporting.WeilVerdierPreservationStrata
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemTransition
public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCompactScalarSquare
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # The coefficient system unit and its finite evaluations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})

/-- Pushforward along an identified ring preserves its regular module.
Source: Stacks 07A4 (blueprint: lem-coef-system-unit-comparison). -/
def integralDualizingPushforwardUnitIso {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u + 1})
    {S : Sheaf J RingCat.{u + 1}}
    (h : (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R = S) :
    (SheafOfModules.pushforward (F := F) (eqToHom h.symm)).obj
      (SheafOfModules.unit R) ≅ SheafOfModules.unit S := by
  subst S
  exact Iso.refl _

/-- Ordinary evaluation sends the coefficient system ring to its finite regular module.
Source: Stacks 0941 (blueprint: lem-coef-system-unit-comparison). -/
def integralDualizingOrdinaryUnitEvaluation (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).obj
      (SheafOfModules.unit
        ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E W))) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n) :=
  integralDualizingPushforwardUnitIso (Prod.sectR n W.ProEt) _
    (coefficientSequenceEvaluationRing_eq l E W n)

/-- Canonical evaluation coordinates for the regular coefficient system.
Source: Stacks 07A4; finite counit compatibility, proof step 2.
(blueprint: lem-coef-system-unit-comparison). -/
def integralDualizingRegularUnitEvaluation (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).obj
      ((DerivedCategory.singleFunctor (coefficientSequenceModules l E W) 0).obj
        (SheafOfModules.unit
          ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (coefficientSequenceCommRingSheaf l E W)))) ≅
    (finiteDualizingRealization l E W n).obj
      (Etale.constantComplex (finiteDualizingCoeff l E n) W) :=
  ((coefficientSequenceEvaluation l E W n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (integralDualizingOrdinaryUnitEvaluation l E W n) ≪≫
    (finiteDualizingIntrinsicUnit l E W n).symm ≪≫
    ((sfIntrinsicDerivedEquivalence W
      (Padic.coefficientExtensionRing l E (n + 1))).functor.mapIso
        (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
          (finiteDualizingCoeff l E n) W)).symm

end WeilConjectures
