/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointSubfieldScalarComparison
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel

import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import all WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import all Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Scalar comparisons and compatibility of the native local return

Source: the scalar-descent sentence of prop-every-iterate-trace.proof.md,
steps 2 and 3 of the derived scalar Frobenius comparison.
(blueprint: def-zl-strict-weil-derived-scalar-comparisons).
Composition coherence and local transport use
(blueprint: lem-zl-strict-weil-scalar-pull-coherence) and
(blueprint: lem-zl-strict-weil-scalar-local-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.StrictWeilDerivedScalar
/-- Ordinary derived extension on module objects along the recorded E-to-Omega map.
Source: latest blueprint, T_T (blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
abbrev change (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (T : Scheme.{u}) :=
  (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ell E)).leftDerivedFunctor

/-- Ordinary derived extension of the scalar section fields.
Source: latest blueprint, tensor_E^L Omega
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
abbrev scalarChange (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :=
  (pointSubfieldSectionExtension.{u} ell E).leftDerivedFunctor

/-- Canonical derived pullback comparison, with exact pullbacks presented termwise.
Source: latest blueprint, chi and the point pullback comparison
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
def pullComparison (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    {T U : Scheme.{u}} (f : T ⟶ U) :
    NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) f ⋙ change ell E T ≅
      change ell E U ⋙ NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) f :=
  Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.continuousMapRingObj E) f).symm
      (change ell E T) ≪≫
    derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ell E) f ≪≫
    Functor.isoWhiskerLeft (change ell E U)
      (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ell) f)

/-- Extension of a strict pair: theta_Omega = T(theta) after chi inverse.
Source: latest blueprint, induced Weil structure
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
def extendedPair (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    {T : Scheme.{u}} (g : T ⟶ T)
    (K : Endofunctor.IsoAlgebra
      (NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) g)) :
    Endofunctor.IsoAlgebra (NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) g) :=
  Endofunctor.IsoAlgebra.mk ((change ell E T).obj K.carrier)
    ((pullComparison ell E g).symm.app K.carrier ≪≫ (change ell E T).mapIso K.str)

/-- The coefficient inclusion bundled only to apply the existing compact-support mate.
Source: latest blueprint, listed inclusion E to Omega
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
def coefficientArrow (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    (⟨Profinite.continuousMapRingObj E⟩ : ScalarSixRing.{u}) ⟶
      (⟨Profinite.padicAlgClRingObj ell⟩ : ScalarSixRing.{u}) :=
  CommMon.homMk ⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩

/-- The canonical comparison from derived point sections to their exact termwise
presentation. The two ordinary section functors are definitionally the same Hom-from-unit
functor with its constant scalar action; this is the derived-functor universal comparison.
Source: latest blueprint, exact final-object sections
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
def sectionComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (D : FiniteFieldDatum.{u}) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    (condensedRingCoefficientSections Λ (Spec (.of D.k))).rightDerivedFunctor ≅
      (NativeCondensedPoint.sections Λ D.k).mapDerivedCategory := by
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact (condensedRingCoefficientSections Λ
    (Spec (.of D.k))).rightDerivedFunctorIsoMapDerivedCategory

/-- The specified b_x: point scalar comparison followed by the pullback comparison,
expressed on the existing native scalar stalks via the canonical exact-section comparison.
Source: latest blueprint, canonical composite defining b_x
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
def stalkComparison (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {Y : Scheme.{u}}
    (K : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E) Y)
    (z : Spec (.of D.k) ⟶ Y) :
    (scalarChange ell E).obj (NativeCondensedDerived.stalk
        (Profinite.continuousMapRingObj E) D K z) ⟶
      NativeCondensedDerived.stalk (Profinite.padicAlgClRingObj ell) D
        ((change ell E Y).obj K) z :=
  (scalarChange ell E).map
      ((sectionComparison (Profinite.continuousMapRingObj E) D).inv.app
        ((NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) z).obj K)) ≫
    (pointComparison ell E D).hom.app
      ((NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) z).obj K) ≫
    (pointAlgClSections ell D.k).rightDerivedFunctor.map
      ((pullComparison ell E z).hom.app K) ≫
    (sectionComparison (Profinite.padicAlgClRingObj ell) D).hom.app
      ((NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) z).obj
        ((change ell E Y).obj K))

/-- The specified stalk comparison as a natural transformation.
Source: composition of the point and inverse-image comparisons in DAG step 2
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
def stalkComparisonNatTrans (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {Y : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ Y) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) z ⋙
        (NativeCondensedPoint.sections
          (Profinite.continuousMapRingObj E) D.k).mapDerivedCategory ⋙
        scalarChange ell E ⟶
      change ell E Y ⋙ NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) z ⋙
        (NativeCondensedPoint.sections
          (Profinite.padicAlgClRingObj ell) D.k).mapDerivedCategory := by
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact Functor.whiskerLeft (NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) z)
      (Functor.whiskerRight (sectionComparison (Profinite.continuousMapRingObj E) D).inv
        (scalarChange ell E)) ≫
    Functor.whiskerLeft (NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) z)
      (pointComparison ell E D).hom ≫
    Functor.whiskerRight (pullComparison ell E z).hom
      (pointAlgClSections ell D.k).rightDerivedFunctor ≫
    Functor.whiskerLeft
      (change ell E Y ⋙ NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) z)
      (sectionComparison (Profinite.padicAlgClRingObj ell) D).hom

/-- Naturality of the actual stalk comparison, on arbitrary derived morphisms.
Source: DAG step 2, naturality of the point and pullback comparisons
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
theorem stalkComparison_naturality (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) {Y : Scheme.{u}}
    (z : Spec (.of D.k) ⟶ Y)
    {K L : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E) Y}
    (f : K ⟶ L) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    (scalarChange ell E).map ((NativeCondensedPoint.sections
        (Profinite.continuousMapRingObj E) D.k).mapDerivedCategory.map
          ((NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) z).map f)) ≫
        stalkComparison D ell E L z =
      stalkComparison D ell E K z ≫
        (NativeCondensedPoint.sections
          (Profinite.padicAlgClRingObj ell) D.k).mapDerivedCategory.map
          ((NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) z).map
            ((change ell E Y).map f)) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact (stalkComparisonNatTrans D ell E z).naturality f

/-- Every factor of the specified stalk comparison is invertible, without boundedness.
Source: DAG step 2, the point scalar isomorphism and the pullback scalar isomorphism
(blueprint: def-zl-strict-weil-derived-scalar-comparisons). -/
theorem stalkComparison_isIso (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {Y : Scheme.{u}}
    (K : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E) Y)
    (z : Spec (.of D.k) ⟶ Y) : IsIso (stalkComparison D ell E K z) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  unfold stalkComparison
  infer_instance

attribute [local irreducible] pullComparison

set_option maxHeartbeats 8000000 in
-- Elaborating scalar comparison compositors needs the larger heartbeat budget.
/-- The scalar comparison intertwines every iterate of the Weil isomorphism.
Source: derived scalar comparison step 8; adjacent comparisons cancel in each induction step
(blueprint: lem-zl-strict-weil-scalar-pull-coherence). -/
theorem pullComparison_iterate (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {Y : Scheme.{u}} (g : Y ⟶ Y)
    (K : Endofunctor.IsoAlgebra
      (NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) g)) (r : ℕ) :
    (pullComparison ell E (NativeCondensedModule.localPositivePower g r)).hom.app K.carrier ≫
        (NativeCondensedDerived.iterate (Profinite.padicAlgClRingObj ell) g
          (extendedPair ell E g K).carrier (extendedPair ell E g K).str r).hom =
      (change ell E Y).map
        (NativeCondensedDerived.iterate (Profinite.continuousMapRingObj E) g
          K.carrier K.str r).hom := by
  let H : (NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) g).obj
        ((change ell E Y).obj K.carrier) ≅ (change ell E Y).obj K.carrier :=
    (pullComparison ell E g).symm.app K.carrier ≪≫ (change ell E Y).mapIso K.str
  simp only [extendedPair, Endofunctor.IsoAlgebra.mk_carrier,
    Endofunctor.IsoAlgebra.mk_str]
  change (pullComparison ell E (NativeCondensedModule.localPositivePower g r)).hom.app
      K.carrier ≫
      (NativeCondensedDerived.iterate (Profinite.padicAlgClRingObj ell) g
        ((change ell E Y).obj K.carrier) H r).hom =
    (change ell E Y).map
      (NativeCondensedDerived.iterate (Profinite.continuousMapRingObj E) g
        K.carrier K.str r).hom
  induction r with
  | zero =>
    simp [NativeCondensedModule.localPositivePower, NativeCondensedDerived.iterate, H]
  | succ r ih =>
    have hc := pullComparison_composition ell E
      (NativeCondensedModule.localPositivePower g r) g K.carrier
    have hn := (pullComparison ell E
      (NativeCondensedModule.localPositivePower g r)).hom.naturality K.str.hom
    have hb : (pullComparison ell E g).hom.app K.carrier ≫ H.hom =
        (change ell E Y).map K.str.hom := by
      simp [H]
    simp only [scalarSixPullComp, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] at hc
    simp only [Functor.comp_map] at hn
    simp only [NativeCondensedModule.localPositivePower, NativeCondensedDerived.iterate,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
    rw [reassoc_of% hc]
    have hm := congrArg
      (fun w ↦ (NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell)
        (NativeCondensedModule.localPositivePower g r)).map w ≫
          (NativeCondensedDerived.iterate (Profinite.padicAlgClRingObj ell) g
            ((change ell E Y).obj K.carrier) H r).hom) hb
    simp only [Functor.map_comp, Category.assoc] at hm
    rw [hm]
    rw [← reassoc_of% hn, ih]

/-- The first local arrow: point reparametrization and the exact pullback compositor.
Source: def-weil-local-frobenius-trace, the arrow before the iterated Weil structure
(blueprint: lem-zl-strict-weil-scalar-local-compatibility). -/
def localTransport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (D : FiniteFieldDatum.{u}) {Y : Scheme.{u}} (g : Y ⟶ Y)
    (M : NativeCondensedDerived.Ambient Λ Y) (z : Spec (.of D.k) ⟶ Y) (r : ℕ)
    (hz : z ≫ NativeCondensedModule.localPositivePower g r =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom r ≫ z) :
    NativeCondensedDerived.stalk Λ D M z ⟶ NativeCondensedDerived.stalk Λ D
      ((NativeCondensedDerived.pull Λ (NativeCondensedModule.localPositivePower g r)).obj M) z :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (NativeCondensedPoint.sections Λ D.k).mapDerivedCategory.map
    ((Functor.mapDerivedCategoryNatIso
      ((Functor.rightUnitor (CondensedRing.upperStar Λ z)).symm ≪≫
        CondensedRing.pointComparison Λ
          (CondensedRing.upperStarIsoIdOfIsSepClosed Λ
            (NativeCondensedModule.localPositivePower
              (NativeCondensedModule.frobeniusPointIso D).hom r))
          (NativeCondensedModule.localPositivePower g r) hz)).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso
        (CondensedRing.upperStar Λ (NativeCondensedModule.localPositivePower g r))
        (CondensedRing.upperStar Λ z)).hom.app M)

/-- Factoring the local operator does not alter its point insertion or its compositor.
Source: def-weil-local-frobenius-trace, defining composite
(blueprint: lem-zl-strict-weil-scalar-local-compatibility). -/
theorem operator_factorization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (D : FiniteFieldDatum.{u}) {Y : Scheme.{u}} (g : Y ⟶ Y)
    (K : Endofunctor.IsoAlgebra (NativeCondensedDerived.pull Λ g))
    (z : Spec (.of D.k) ⟶ Y) (r : ℕ)
    (hz : z ≫ NativeCondensedModule.localPositivePower g r =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom r ≫ z) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    NativeCondensedDerived.operator Λ D g K.carrier K.str z r hz =
      localTransport Λ D g K.carrier z r hz ≫
        (NativeCondensedPoint.sections Λ D.k).mapDerivedCategory.map
          ((NativeCondensedDerived.pull Λ z).map
            (NativeCondensedDerived.iterate Λ g K.carrier K.str r).hom) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  simp only [NativeCondensedDerived.operator, localTransport,
    Functor.map_comp, Category.assoc]

/-- Scalar extension commutes with the specified unstructured local return arrow.
There is no Weil structure, constructibility or perfectness assumption here.
Source: derived scalar comparison, steps 5 and 8, expanding the scalar-descent sentence
of latest prop-every-iterate-trace.proof.md
(blueprint: lem-zl-strict-weil-scalar-local-compatibility).

Proof: apply composition coherence of the normalized coefficient/pullback comparisons
to the equality z g^(r+1)=g_s^(r+1) z. This identifies the two routes through its
pullback square. The inverse point trivialization is the canonical inverse-image
insertion along g_s^(r+1). The normalized balanced tensor comparison takes m tensor c
to the reparametrized m tensor the same constant c, since the coefficient map is pulled
from the point. Hence its square with scalar extension commutes on balanced generators.
The point scalar comparison is determined by its pure-tensor normalization; compute
this same square on flat-term K-flat complexes. Exact inverse image, exact sections,
and exact field extension descend the equation through localization. The derived-unit
and counit normalizations identify the result with the chosen pointComparison and the
specified sectionComparison, rather than with an independently chosen isomorphism.
Paste the point square with the composition square. Its final endpoint correction is
exactly inverse pullComparison for g^(r+1), as shown on the right. -/
theorem localTransport_scalar (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {Y : Scheme.{u}} (g : Y ⟶ Y)
    (M : NativeCondensedDerived.Ambient (Profinite.continuousMapRingObj E) Y)
    (z : Spec (.of D.k) ⟶ Y) (r : ℕ)
    (hz : z ≫ NativeCondensedModule.localPositivePower g r =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom r ≫ z) :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    (scalarChange ell E).map
        (localTransport (Profinite.continuousMapRingObj E) D g M z r hz) ≫
        stalkComparison D ell E
          ((NativeCondensedDerived.pull (Profinite.continuousMapRingObj E)
            (NativeCondensedModule.localPositivePower g r)).obj M) z =
      stalkComparison D ell E M z ≫
        localTransport (Profinite.padicAlgClRingObj ell) D g
          ((change ell E Y).obj M) z r hz ≫
        (NativeCondensedPoint.sections (Profinite.padicAlgClRingObj ell) D.k
          ).mapDerivedCategory.map
          ((NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) z).map
            ((pullComparison ell E (NativeCondensedModule.localPositivePower g r)).inv.app M)) := by
  sorry

attribute [local irreducible] stalkComparison
  NativeCondensedDerived.iterate NativeCondensedDerived.operator

set_option maxHeartbeats 8000000 in
-- Keep operator factorization and scalar comparison rewriting within one budget.
/-- Naturality at the iterated Weil isomorphism converts local transport compatibility
into compatibility of the actual local return operators.
Source: derived scalar comparison, step 8
(blueprint: lem-zl-strict-weil-scalar-local-compatibility). -/
theorem stalkComparison_operator (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {Y : Scheme.{u}} (g : Y ⟶ Y)
    (K : Endofunctor.IsoAlgebra
      (NativeCondensedDerived.pull (Profinite.continuousMapRingObj E) g))
    (z : Spec (.of D.k) ⟶ Y) (r : ℕ)
    (hz : z ≫ NativeCondensedModule.localPositivePower g r =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom r ≫ z) :
    (scalarChange ell E).map
        (NativeCondensedDerived.operator (Profinite.continuousMapRingObj E) D
          g K.carrier K.str z r hz) ≫ stalkComparison D ell E K.carrier z =
      stalkComparison D ell E K.carrier z ≫
        NativeCondensedDerived.operator (Profinite.padicAlgClRingObj ell) D g
          (extendedPair ell E g K).carrier (extendedPair ell E g K).str z r hz := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hi : (pullComparison ell E (NativeCondensedModule.localPositivePower g r)).inv.app
        K.carrier ≫ (change ell E Y).map
          (NativeCondensedDerived.iterate (Profinite.continuousMapRingObj E) g
            K.carrier K.str r).hom =
      (NativeCondensedDerived.iterate (Profinite.padicAlgClRingObj ell) g
        (extendedPair ell E g K).carrier (extendedPair ell E g K).str r).hom := by
    rw [← pullComparison_iterate ell E g K r, Iso.inv_hom_id_app_assoc]
  have ht := congrArg
    (fun f ↦ (NativeCondensedPoint.sections (Profinite.padicAlgClRingObj ell) D.k
      ).mapDerivedCategory.map
        ((NativeCondensedDerived.pull (Profinite.padicAlgClRingObj ell) z).map f)) hi
  simp only [Functor.map_comp] at ht
  rw [operator_factorization (Profinite.continuousMapRingObj E) D g K z r hz,
    operator_factorization (Profinite.padicAlgClRingObj ell) D g
      (extendedPair ell E g K) z r hz, Functor.map_comp, Category.assoc,
    stalkComparison_naturality D ell E z
      (NativeCondensedDerived.iterate (Profinite.continuousMapRingObj E) g
        K.carrier K.str r).hom,
    ← Category.assoc, localTransport_scalar D ell E g K.carrier z r hz]
  simp only [Category.assoc]
  simp only [extendedPair, Endofunctor.IsoAlgebra.mk_carrier,
    Endofunctor.IsoAlgebra.mk_str] at ht ⊢
  rw [ht]

end WeilConjectures.StrictWeilDerivedScalar
