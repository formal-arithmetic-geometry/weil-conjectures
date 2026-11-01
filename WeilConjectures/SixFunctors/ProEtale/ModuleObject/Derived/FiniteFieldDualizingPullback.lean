/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.InverseImageModuleFlat
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoverRestrictionConservative
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteCompactSupportExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.SepFinType
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.Compactification.Triangle
import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Refinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchangeTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedCoefficientIsoExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.LocalizingIsoLocus
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.AlgebraicGeometry.Etale.EtaleHorizontalSupportMate
import Mathlib.FieldTheory.Separable
import WeilConjectures.FieldTheory.TensorProductDiagonal
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison

/-!
# Finite-field dualizing-object pullback

Source: latest blueprint, `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(blueprint: lem-sf-finite-field-dualizing-pullback).

The dualizing objects are specified by their constructible adjunction counits. The compact
support functors and exchange are the published compactification constructions, and the Hom
comparison is the evaluation transpose of the canonical tensorator.
-/

@[expose] public section
set_option autoImplicit false

universe u v w uC vC uD vD uB vB uB' vB'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The discrete condensed finite quotient coefficient of the finite-field comparison.
Source: blueprint finite-field paragraph, coefficient A
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDualizingCoefficient
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E] (n : ℕ) :
    CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
  let A := Padic.coefficientExtensionRing ell E n
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  letI : IsTopologicalRing A := DiscreteTopology.topologicalRing
  let R := Profinite.continuousMapRingObjOfUniverse.{u, u} A
  letI : MonObj R := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  letI : IsCommMonObj R := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A
  exact CommMon.mk R

/-- The actual module-object derived category, with its relative derived tensor and Hom.
Source: blueprint finite-field paragraph, D(Mod A_V)
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
abbrev finiteFieldModuleDerived
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ.X X))

/-- The canonical dualizing-Hom comparison: evaluation transpose followed by Hom(1,w).
Source: blueprint finite-field paragraph, comparison c_K
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDualizingHomComparison
    {C : Type v} {D : Type w} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (G : C ⥤ D) [G.Monoidal] (K W : C) (W' : D) (e : G.obj W ≅ W') :
    G.obj ((ihom K).obj W) ⟶ (ihom (G.obj K)).obj W' :=
  (Functor.LaxMonoidal.ihomComparison G K).natTrans.app W ≫ (ihom (G.obj K)).map e.hom

/-- The specified Koszul braiding on the actual module-object derived category.
Source: blueprint finite-field paragraph, symmetric tensor identifications
(blueprint: lem-sf-finite-field-dualizing-pullback). -/
noncomputable def finiteFieldDerivedBraiding
    (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (X : Scheme.{u}) (K L : finiteFieldModuleDerived Λ X) : K ⊗ L ≅ L ⊗ K :=
  @BraidedCategory.braiding _ _ _
    (DerivedCategory.braidedCategory'
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))) K L

end AlgebraicGeometry.ProEtale.CondensedRing
