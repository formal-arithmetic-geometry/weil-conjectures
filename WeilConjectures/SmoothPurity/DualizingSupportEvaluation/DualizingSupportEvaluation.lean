/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DualizingSupportEvaluation.CompactSupportCoefficientMateNormalization
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SixFunctors.Finite.FiniteDualizing
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompactSupportRestriction
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Compact.CompactCoefficientComposition
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.SixFunctors.Supporting.WeilVerdierPreservationStrata
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemTransition
import all WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCompactScalarSquare

/-! # Evaluated compact support and scalar-adjunction transitions

Source: blueprint `prop-coef-integral-dualizing.proof.md`, paragraph 2,
specified finite maps before limits (blueprint: lem-coef-dualizing-support-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.DualizingSupportEvaluation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary compact support on the whole sequence site, with j_! exact and Rp_*
derived on systems. Source: blueprint paragraph 2, before limits
(blueprint: lem-coef-dualizing-support-evaluation). -/
def support {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y :=
  ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g

/-- c is the proper coefficient mate followed by the exact open coefficient map,
transported only by the specified direct-image presentation.
Source: blueprint paragraph 2; Stacks 0GL1, 0D6E
(blueprint: lem-coef-dualizing-support-evaluation). -/
def comparison {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) Y ⟶
      scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) X ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  coefficientMateComparison l E c h

section TowerProofs

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
attribute [local implicit_reducible] SemilinearSections.moduleAbelian
  SemilinearSections.hasDerived coefficientSequenceHasDerived
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientFiniteDerivedRestriction scalarReductionDerivedRestriction
  coefficientConstantTowerEvaluation coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
  reductionModulesHasDerivedCategory proEtaleRingModules_hasDerivedCategory
  compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition
  sections target support B sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

end TowerProofs

section SiteProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

attribute [local irreducible] Etale.DerivedCategory.hasTorAmplitudeIn
  DerivedCategory.TStructure.t pbcFixedScalarExtension

attribute [local irreducible]
  CoefficientCompatibility.transportedRecordedReductionDirectImageComparison
  compactSupportSiteComparison comparisonUpperStar pbcComparisonReduction
  Etale.compactScalarMap Etale.ExceptionalCoefficients.compactSupportMap
  Functor.leftDerivedFunctor DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian

end SiteProof

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

attribute [local implicit_reducible] SemilinearSections.moduleAbelian
  SemilinearSections.hasDerived coefficientSequenceHasDerived
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientFiniteDerivedRestriction scalarReductionDerivedRestriction
  coefficientConstantTowerEvaluation coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived
  reductionModulesHasDerivedCategory proEtaleRingModules_hasDerivedCategory
  compactSupportSystemLevel compactSupportSystemQuotient
  ProEtale.VaryingRing.coefficientTransition coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition
  sections target support B sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat

attribute [local implicit_reducible] catToReflQuiver

end WeilConjectures.DualizingSupportEvaluation
