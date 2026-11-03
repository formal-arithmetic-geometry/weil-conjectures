/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
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
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
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
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.ReductionDirectImageFiniteCoefficients
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.SmoothPurity.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.AlgebraicGeometry.ScalarIdentification.ScalarRightUnitEncoding
public import WeilConjectures.AlgebraicGeometry.ScalarRightUnitNative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension

/-!
# Pro-etale scalar-extension right unit

The current-model scalar computation helpers and the tensor and unit maps
are constructed here on K-flat representatives,
using the actual scalar computation counit and the normalized balanced cochain
maps. The theorem states their right-unit law and the equations identifying
them with the condensed scalar comparisons and compact-support comparison.

Source: Stacks Tags 03EK, 06YY and 07A4; blueprint
`det-sp-reduction-compatibilities`, Proof (3), Tensor map.
(blueprint: lem-pur-scalar-right-unit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
open MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale

/-- The explicit size bound of the actual small pro-etale site.
Source: the small-site convention, Stacks 0991
(blueprint: lem-pur-scalar-right-unit).
Proof: the small pro-etale site of `T` has objects and morphisms in `Type u`, hence
in `Type (u + 1)`; it is therefore essentially small in that universe, being
equivalent to itself (`essentiallySmallSelf`). -/
theorem currentScalarSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt := by
  exact essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] currentScalarSmall

/-- Ordinary extension in the current ringed-site universal pair, fixed on objects
and maps by sheafified balanced tensor. Source: Stacks 03CY, 06YY
(blueprint: lem-pur-scalar-right-unit). -/
def currentScalarOrdinary {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    proEtaleRingModules T (proEtaleConstantRing T A) ⥤
      proEtaleRingModules T (proEtaleConstantRing T B) :=
  (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (C := T.ProEt) (J := ProEt.topology T)
    (O := proEtaleConstantRing T A) (O' := proEtaleConstantRing T B)
    (proEtaleConstantRingMap (T := T) φ)).choose

/-- Object normalization of the current ordinary extension.
Source: Stacks 03CY (blueprint: lem-pur-scalar-right-unit).
Proof: the object clause of the current derived-change-of-rings theorem. -/
theorem currentScalarOrdinary_obj {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : proEtaleRingModules T (proEtaleConstantRing T A)) :
    (currentScalarOrdinary φ T).obj M =
      SheafOfModules.changeOfRings (proEtaleConstantRingMap (T := T) φ) M := by
  exact (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (C := T.ProEt) (J := ProEt.topology T)
    (O := proEtaleConstantRing T A) (O' := proEtaleConstantRing T B)
    (proEtaleConstantRingMap (T := T) φ)).choose_spec.choose M

/-- Additivity from the same normalized current universal pair.
Source: Stacks 03CY (blueprint: lem-pur-scalar-right-unit).
Proof: the current derived-change-of-rings theorem, whose ordinary functor is
`currentScalarOrdinary`, supplies additivity of that same functor as its third clause;
equivalently, sheafified balanced tensor with `B_T` is additive in the module. -/
theorem currentScalarOrdinaryAdditive {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : (currentScalarOrdinary φ T).Additive := by
  exact (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (C := T.ProEt) (J := ProEt.topology T)
    (O := proEtaleConstantRing T A) (O' := proEtaleConstantRing T B)
    (proEtaleConstantRingMap (T := T) φ)).choose_spec.choose_spec.choose_spec.choose

attribute [local instance] currentScalarOrdinaryAdditive

/-- The ordinary identification with the explicit balanced extension functor.
Source: Stacks 03CY (blueprint: lem-pur-scalar-right-unit). -/
def currentScalarOrdinaryComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    currentScalarOrdinary φ T ≅
      CochainPullback.extensionFunctor.{u + 1, u + 1, u}
        (proEtaleConstantRingMap (T := T) φ) :=
  NatIso.ofComponents (fun M ↦ eqToIso (currentScalarOrdinary_obj φ T M)) (by
    intro M N g
    have h :=
      (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
        (C := T.ProEt) (J := ProEt.topology T)
    (O := proEtaleConstantRing T A) (O' := proEtaleConstantRing T B)
    (proEtaleConstantRingMap (T := T) φ)).choose_spec.choose_spec.choose g
    dsimp only [eqToIso.hom]
    erw [h]
    simp [CochainPullback.extensionFunctor])

/-- The normalized comparison termwise on unbounded complexes.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-right-unit). -/
def currentScalarComplexComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (currentScalarOrdinary φ T).mapHomologicalComplex (.up ℤ) ≅
      CochainPullback.extend.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ) :=
  NatIso.mapHomologicalComplex (currentScalarOrdinaryComparison φ T) (.up ℤ)

/-- The universal homotopy counit of the current ringed-site construction.
The existing scalar functor is the same selected universal pair. No comparison
with an independently chosen functor is used.
Source: Stacks 06XN, 06YY (blueprint: lem-pur-scalar-right-unit). -/
def currentScalarHomotopyCounit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ scalarExtensionFunctor φ T ⟶
      (currentScalarOrdinary φ T).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
  let h := (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (C := T.ProEt) (J := ProEt.topology T)
    (O := proEtaleConstantRing T A) (O' := proEtaleConstantRing T B)
    (proEtaleConstantRingMap (T := T) φ)).choose_spec.choose_spec.choose_spec.choose_spec.2.2
  exact h.choose_spec.choose

/-- The actual computation counit, with explicit current-model cochain target.
Source: Stacks 06YY, 07A4 (blueprint: lem-pur-scalar-right-unit). -/
def currentScalarCounitNat {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ scalarExtensionFunctor φ T ⟶
      CochainPullback.extend.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ) ⋙
        DerivedCategory.Q := by
  let E := currentScalarOrdinary φ T
  let F := scalarExtensionFunctor φ T
  let q := HomotopyCategory.quotient
    (proEtaleRingModules T (proEtaleConstantRing T A)) (.up ℤ)
  let j : q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _)
  exact Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv F ≫
    (Functor.associator q DerivedCategory.Qh F).hom ≫
    Functor.whiskerLeft q (currentScalarHomotopyCounit φ T) ≫ j.hom ≫
    Functor.whiskerRight (currentScalarComplexComparison φ T).hom DerivedCategory.Q

/-- The component of the current-model computation counit.
Source: Stacks 06YY (blueprint: lem-pur-scalar-right-unit). -/
def currentScalarCounit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ) :
    (scalarExtensionFunctor φ T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((CochainPullback.extend.{u + 1, u + 1, u}
          (proEtaleConstantRingMap (T := T) φ)).obj P) :=
  (currentScalarCounitNat φ T).app P

/-- K-flat computation through the current-model counit.
Source: Stacks 06YS, 06YY (blueprint: lem-pur-scalar-right-unit).
Proof: the current universal homotopy counit computes on K-flat representatives.
The quotient factorization and normalized ordinary comparison are isomorphisms,
so their composite remains invertible. -/
theorem currentScalarCounit_isIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing T A) P) :
    IsIso (currentScalarCounit φ T P) := by
  let h := (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (C := T.ProEt) (J := ProEt.topology T)
    (O := proEtaleConstantRing T A) (O' := proEtaleConstantRing T B)
    (proEtaleConstantRingMap (T := T) φ)).choose_spec.choose_spec.choose_spec.choose_spec.2.2
  have : IsIso ((currentScalarHomotopyCounit φ T).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    h.choose_spec.choose_spec.2.2 P hP
  dsimp [currentScalarCounit, currentScalarCounitNat]
  infer_instance

/-- Canonical current-model computation iso, with its target-ring action retained.
Source: Stacks 06YY (blueprint: lem-pur-scalar-right-unit). -/
def currentScalarKFlatIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing T A) P) :
    (scalarExtensionFunctor φ T).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        ((CochainPullback.extend.{u + 1, u + 1, u}
          (proEtaleConstantRingMap (T := T) φ)).obj P) :=
  @asIso _ _ _ _ (currentScalarCounit φ T P) (currentScalarCounit_isIso φ T P hP)

/-- Morphisms compute by termwise balanced extension using this same counit.
Source: Stacks 06YY (blueprint: lem-pur-scalar-right-unit).
Proof: naturality of the displayed current-model counit. -/
theorem currentScalar_map {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {P Q : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ}
    (v : P ⟶ Q) :
    (scalarExtensionFunctor φ T).map (DerivedCategory.Q.map v) ≫ currentScalarCounit φ T Q =
      currentScalarCounit φ T P ≫ DerivedCategory.Q.map
        ((CochainPullback.extend.{u + 1, u + 1, u}
          (proEtaleConstantRingMap (T := T) φ)).map v) := by
  exact (currentScalarCounitNat φ T).naturality v

/-- The published derived tensor is the SheafOfModules tensor localized with
the RingedDerivedNative K-flat construction.
Source: Stacks 06YS and 0FPT (blueprint: lem-pur-scalar-right-unit). -/
@[instance_reducible]
noncomputable def proEtaleDerivedMonoidal
    {A : Type u} [CommRing A] (T : Scheme.{u}) :
    MonoidalCategory (proEtaleDerivedCategory T A) :=
  CategoryTheory.RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2}
    (C := T.ProEt) (ProEt.topology T) (proEtaleConstantRing T A)

/-- Complexes of ordinary constant-ring modules.
Source: Stacks 06YY (blueprint: lem-pur-scalar-right-unit). -/
abbrev ScalarComplex (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ

/-- The ordinary sheaf tensor used by total complexes.
Source: Stacks 03EK (blueprint: lem-pur-scalar-right-unit). -/
@[instance_reducible]
def scalarModulesMonoidal (T : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalCategory (proEtaleRingModules T (proEtaleConstantRing T A)) :=
  SheafOfModules.cochainModulesMonoidal (proEtaleConstantRing T A)
/-- Additivity of this ordinary sheaf tensor.
Source: Stacks 03EK (blueprint: lem-pur-scalar-right-unit).
Proof: the sheaf tensor is sheafification of the sectionwise tensor of modules, which
is additive in each variable; sheafification is additive. This is the published
`SheafOfModules.cochainModulesPreadditive` for the ring `A_T`. -/
theorem scalarModulesPreadditive (T : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalPreadditive (proEtaleRingModules T (proEtaleConstantRing T A)) := by
  exact SheafOfModules.cochainModulesPreadditive (proEtaleConstantRing T A)

/-- Use the native K-flat derived tensor for the displayed tensor notation.
Source: Stacks 06YS, 0FPT (blueprint: lem-pur-scalar-right-unit). -/
@[instance_reducible]
def scalarMonoidal (T : Scheme.{u}) (A : Type u) [CommRing A] :
    MonoidalCategory (proEtaleDerivedCategory T A) := proEtaleDerivedMonoidal T

attribute [local instance] scalarModulesMonoidal scalarModulesPreadditive scalarMonoidal

/-- Balanced total comparison: on a pure summand it is
`(x ⊗ y) ⊗ b ↦ (x ⊗ b) ⊗ (y ⊗ 1)`.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-right-unit). -/
def scalarComplexTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (P Q : ScalarComplex T A) :
    (CochainPullback.extend.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ)).obj (P ⊗ Q) ≅
      (CochainPullback.extend.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ)).obj P ⊗
        (CochainPullback.extend.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ)).obj Q :=
  CochainPullback.epsilon.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ) P Q

/-- Balanced unit comparison, `a ⊗ b ↦ φ(a)b` in degree zero.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-scalar-right-unit). -/
def scalarComplexUnit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (CochainPullback.extend.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ)).obj
      (𝟙_ (ScalarComplex T A)) ≅ 𝟙_ (ScalarComplex T B) :=
  CochainPullback.unit
      (CochainPullback.extensionPullback.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ))
      (CochainPullback.extensionComparison.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ))

/-- A flat-term K-flat representative, with its specified isomorphism to the input.
Source: Stacks 06YS, 06YT (blueprint: lem-pur-scalar-right-unit). -/
structure ScalarFlatRepresentative {A : Type u} [CommRing A]
    (T : Scheme.{u}) (K : proEtaleDerivedCategory T A) where
  complex : ScalarComplex T A
  kflat : CochainComplex.IsKFlatIndependentCoefficients
    (R := proEtaleConstantRing T A) complex
  flat : ∀ i : ℤ, exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _
      (SheafOfModules.monoidalCategory (proEtaleConstantRing T A)) (complex.X i))
  iso : DerivedCategory.Q.obj complex ≅ K

/-- Choose only a resolution, whose effect on the comparison will be independent
of the choice by its representative normalization equation below.
Source: Stacks 06YS, 06YT (blueprint: lem-pur-scalar-right-unit). -/
def scalarFlatRepresentative {A : Type u} [CommRing A]
    (T : Scheme.{u}) (K : proEtaleDerivedCategory T A) : ScalarFlatRepresentative T K := by
  let h := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (R := proEtaleConstantRing T A) (DerivedCategory.Q.objPreimage K)
  let P := h.choose
  let p := h.choose_spec.choose
  have hp := h.choose_spec.choose_spec
  letI := hp.2.2.1
  exact ⟨P, hp.1, hp.2.1, asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso K⟩

/-- The concrete scalar tensor comparison, constructed on chosen flat-term K-flat
representatives using the balanced cochain map and the actual scalar counit.
Source: Stacks 06YY, 07A4; blueprint Proof (3), Tensor map
(blueprint: lem-pur-scalar-right-unit). -/
def proEtaleScalarTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K L : proEtaleDerivedCategory T A) :
    (scalarExtensionFunctor φ T).obj (K ⊗ L) ⟶
      (scalarExtensionFunctor φ T).obj K ⊗ (scalarExtensionFunctor φ T).obj L := by
  let P := scalarFlatRepresentative T K
  let Q := scalarFlatRepresentative T L
  let E := CochainPullback.extensionFunctor.{u + 1, u + 1, u}
    (proEtaleConstantRingMap (T := T) φ)
  let EP := (E.mapHomologicalComplex (.up ℤ)).obj P.complex
  let EQ := (E.mapHomologicalComplex (.up ℤ)).obj Q.complex
  have hEP := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
    (proEtaleConstantRingMap (T := T) φ) P.complex E (fun _ ↦ rfl)
    (fun g ↦ CochainPullback.extensionFunctor_mapPresentation
      (proEtaleConstantRingMap (T := T) φ) g) P.kflat P.flat).1
  let iA := RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T A) P.complex Q.complex (Or.inl P.kflat)
  let iB := RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T B) EP EQ (Or.inl hEP)
  let cP := currentScalarKFlatIso φ T P.complex P.kflat
  let cQ := currentScalarKFlatIso φ T Q.complex Q.kflat
  exact (scalarExtensionFunctor φ T).map ((tensorIso P.iso Q.iso).inv ≫ iA.inv) ≫
    currentScalarCounit φ T (P.complex ⊗ Q.complex) ≫
    DerivedCategory.Q.map (scalarComplexTensor φ T P.complex Q.complex).hom ≫
    iB.hom ≫ (cP.inv ⊗ₘ cQ.inv) ≫
    ((scalarExtensionFunctor φ T).map P.iso.hom ⊗ₘ
      (scalarExtensionFunctor φ T).map Q.iso.hom)

/-- The actual unit map, via the native localization unit, scalar computation
counit and multiplication on the representative ring in degree zero.
Source: Stacks 03EL, 06YY; blueprint Proof (3), Tensor map
(blueprint: lem-pur-scalar-right-unit). -/
def proEtaleScalarUnit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (scalarExtensionFunctor φ T).obj (𝟙_ (proEtaleDerivedCategory T A)) ⟶
      𝟙_ (proEtaleDerivedCategory T B) :=
  (scalarExtensionFunctor φ T).map
    (RingedDerivedNative.unitIso.{u + 1, u, 0, u + 2}
      (ProEt.topology T) (proEtaleConstantRing T A)).hom ≫
    currentScalarCounit φ T (𝟙_ (ScalarComplex T A)) ≫
    DerivedCategory.Q.map (scalarComplexUnit φ T).hom ≫
    (RingedDerivedNative.unitIso.{u + 1, u, 0, u + 2}
      (ProEt.topology T) (proEtaleConstantRing T B)).inv

/-- Normalization on every flat-term K-flat pair, with the actual computation
counits. This is an equation about the concrete map, not freely supplied data.
Source: Stacks 06YY, 07A4; blueprint Proof (3), Tensor map
(blueprint: lem-pur-scalar-right-unit). -/
def ProEtaleScalarTensorNormalized {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : Prop :=
  letI := RingedDerivedNative.lax.{u + 1, u, 0, u + 2}
    (ProEt.topology T) (proEtaleConstantRing T B)
  ∀ (P Q : ScalarComplex T A)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing T A) P)
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients (R := proEtaleConstantRing T A) Q),
    (∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (proEtaleConstantRing T A)) (P.X i))) →
    (∀ i : ℤ, exactFunctor _ _
      (@MonoidalCategory.tensorRight _ _
        (SheafOfModules.monoidalCategory (proEtaleConstantRing T A)) (Q.X i))) →
    (scalarExtensionFunctor φ T).map
        (RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
          (ProEt.topology T) (proEtaleConstantRing T A) P Q (Or.inl hP)).hom ≫
      proEtaleScalarTensor φ T (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
      (currentScalarCounit φ T P ⊗ₘ currentScalarCounit φ T Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((CochainPullback.extend.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ)).obj P)
        ((CochainPullback.extend.{u + 1, u + 1, u} (proEtaleConstantRingMap (T := T) φ)).obj Q) =
    currentScalarCounit φ T (P ⊗ Q) ≫
      DerivedCategory.Q.map (scalarComplexTensor φ T P Q).hom

/-- Unit normalization as the actual localization/counit square.
Source: Stacks 03EL, 06YY; blueprint Proof (3), Tensor map
(blueprint: lem-pur-scalar-right-unit). -/
def ProEtaleScalarUnitNormalized {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) : Prop :=
  (scalarExtensionFunctor φ T).map
      (RingedDerivedNative.unitIso.{u + 1, u, 0, u + 2}
        (ProEt.topology T) (proEtaleConstantRing T A)).hom ≫
    currentScalarCounit φ T (𝟙_ (ScalarComplex T A)) ≫
    DerivedCategory.Q.map (scalarComplexUnit φ T).hom =
  proEtaleScalarUnit φ T ≫
    (RingedDerivedNative.unitIso.{u + 1, u, 0, u + 2}
      (ProEt.topology T) (proEtaleConstantRing T B)).hom

namespace ScalarIdentification
open FiniteDiscreteOrdinary
open CategoryTheory.InternalAbelianSheafModule

/-- Identify the encoded module with its specified section-action presentation.
Source: Stacks 00YV; blueprint ordinary/internal identification
(blueprint: lem-pur-scalar-right-unit). -/
def moduleIso {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {T : Scheme.{u}} (e : Encoding A T) (M : Internal A T) :
    e.ordinary.functor.obj M ≅ (sectionEncoding A T e.ringIso).obj M :=
  eqToIso (congrArg (fun F ↦ F.obj M) e.ordinary_functor)

/-- An encoding with tensor comparisons fixed on pure sections, total summands,
and localization squares. These equations exclude arbitrary monoidal structures.
Source: Stacks 03EK, 06YN, 06YY; blueprint Proof (3), Tensor map
(blueprint: lem-pur-scalar-right-unit). -/
structure EncodingTensor {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (T : Scheme.{u}) where
  encoding : Encoding A T
  ordinaryCore : encoding.ordinary.functor.CoreMonoidal
  ordinary_tensor : ∀ (M N : Internal A T) (U : T.ProEtᵒᵖ)
      (x : M.X.obj.obj U) (y : N.X.obj.obj U),
    (((moduleIso encoding (M ⊗ N)).inv ≫ (ordinaryCore.μIso M N).inv ≫
      ((moduleIso encoding M).hom ⊗ₘ (moduleIso encoding N).hom)).val.app U)
        (comparison_internalTmul (ProEt.topology T) (condensedRingObj (coefficient A) T)
          M N U x y) =
      SheafOfModules.ScalarHomOrdinary.pure (proEtaleConstantRing T A)
        ((sectionEncoding A T encoding.ringIso).obj M)
        ((sectionEncoding A T encoding.ringIso).obj N) U x y
  ordinary_unit : ∀ (U : T.ProEtᵒᵖ)
      (r : (condensedRingObj (coefficient A) T).obj.obj U),
    (((moduleIso encoding (𝟙_ _)).inv ≫ ordinaryCore.εIso.inv).val.app U) r =
      encoding.ringIso.inv.hom.app U r
  totalTensor : ∀ P Q : CochainComplex (Internal A T) ℤ,
    (encoding.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      (encoding.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj P ⊗
        (encoding.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj Q
  total_summand : ∀ (P Q : CochainComplex (Internal A T) ℤ)
      (p q n : ℤ) (h : p + q = n),
    encoding.ordinary.functor.map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫
      (totalTensor P Q).hom.f n =
    (ordinaryCore.μIso (P.X p) (Q.X q)).inv ≫
      CochainComplex.ιMapBifunctor
        ((encoding.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj P)
        ((encoding.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor _) p q n h
  totalUnit : (encoding.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj
    (𝟙_ (CochainComplex (Internal A T) ℤ)) ≅ 𝟙_ (ScalarComplex T A)
  total_unit : totalUnit.hom.f 0 = ordinaryCore.εIso.inv
  derivedCore : encoding.ordinaryDerived.functor.CoreMonoidal
  derived_tensor :
    letI := RingedDerivedNative.lax.{u + 1, u, 0, u + 2}
      (ProEt.topology T) (proEtaleConstantRing T A)
    ∀ P Q : CochainComplex (Internal A T) ℤ,
      encoding.ordinaryDerived.functor.map (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 1} P Q) ≫
        encoding.ordinary.functor.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (totalTensor P Q).hom =
      (derivedCore.μIso (DerivedCategory.Q.{u + 1}.obj P) (DerivedCategory.Q.{u + 1}.obj Q)).inv ≫
        (encoding.ordinary.functor.mapDerivedCategoryFactors.hom.app P ⊗ₘ
          encoding.ordinary.functor.mapDerivedCategoryFactors.hom.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((encoding.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj P)
          ((encoding.ordinary.functor.mapHomologicalComplex (.up ℤ)).obj Q)
  derived_unit :
    derivedCore.εIso.inv ≫
      (RingedDerivedNative.unitIso.{u + 1, u, 0, u + 2}
        (ProEt.topology T) (proEtaleConstantRing T A)).hom =
    encoding.ordinaryDerived.functor.map (Functor.LaxMonoidal.ε DerivedCategory.Q.{u + 1}) ≫
      encoding.ordinary.functor.mapDerivedCategoryFactors.hom.app (𝟙_ _) ≫
      DerivedCategory.Q.map totalUnit.hom

/-- Small section-module localizations, obtained from the published Grothendieck
abelian theorem; these are separate from the standard ordinary localizations.
Source: Stacks 079Z, 05RU (blueprint: lem-pur-scalar-right-unit). -/
@[instance_reducible]
def sectionDerivedCategories (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    ∀ T : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules (coefficient A) T) := fun T ↦ by
  letI : IsGrothendieckAbelian.{u + 1}
      (ModuleRingedComparison.modules (coefficient A) T) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology T) _
  exact HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [local instance] sectionDerivedCategories

/-- The ordinary identification selected by the recorded coefficient-equivalence
node. The Encoding's ring map and section-action functor are normalized.
Source: blueprint ordinary/internal identification, steps 1--4
(blueprint: lem-pur-scalar-right-unit). -/
def ordinaryEncoding (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    Encoding A T :=
  (moduleObject_ordinary_coefficient_equivalence A).choose T

/-- Direct-image encoding fixed by the identity on all additive sections.
Its derived and open companions below are constructed from this comparison,
not supplied as free compact-support isomorphisms.
Source: Stacks 00YV, 015F; blueprint Proof (3), Tensor map
(blueprint: lem-pur-scalar-right-unit). -/
structure GeometricEncoding {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    (E : ∀ T : Scheme.{u}, Encoding A T) where
  push : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    CondensedRing.lowerStar (coefficient A) f ⋙ (E Y).ordinary.functor ≅
      (E X).ordinary.functor ⋙ proEtaleConstantRingPushforward A f
  push_sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Internal A X)
      (U : Y.ProEtᵒᵖ) (x : ((CondensedRing.lowerStar (coefficient A) f).obj M).X.obj.obj U),
    (((moduleIso (E Y) ((CondensedRing.lowerStar (coefficient A) f).obj M)).inv ≫
      (push f).hom.app M ≫
      (proEtaleConstantRingPushforward A f).map (moduleIso (E X) M).hom).val.app U) x = x

/-- The pullback comparison is the mate of the normalized identity on direct-image
sections through the actual geometric adjunctions and coefficient equivalences.
Source: Stacks 00YV, 03D2 (blueprint: lem-pur-scalar-right-unit). -/
def geometricPullback {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    {E : ∀ T : Scheme.{u}, Encoding A T} (g : GeometricEncoding E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.upperStar (coefficient A) f ⋙ (E X).ordinary.functor ≅
      (E Y).ordinary.functor ⋙ proEtaleConstantRingPullback A f := by
  let ET := (E Y).ordinary
  let EU := (E X).ordinary
  let k := Iso.isoCompInverse (H := ET) (g.push f) ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp (proEtaleConstantRingAdjunction A f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

/-- The open comparison is the uniquely adjunction-compatible left-adjoint
comparison, using the section-unit-normalized ordinary pullback coordinates.
Source: Stacks 03DI, 03DJ (blueprint: lem-pur-scalar-right-unit). -/
def geometricOpen {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    {E : ∀ T : Scheme.{u}, Encoding A T} (g : GeometricEncoding E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙ (E Y).ordinary.functor ≅
      (E X).ordinary.functor ⋙ sfIntrinsicExtensionByZero j A := by
  let ET := (E Y).ordinary
  let EU := (E X).ordinary
  let i := geometricPullback g j
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (coefficient A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- Right-derive the specified direct-image encoding using the universal derived
comparison; no derived direct-image isomorphism is chosen independently.
Source: Stacks 015F, 07A5 (blueprint: lem-pur-scalar-right-unit). -/
def geometricDerivedPush {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    {E : ∀ T : Scheme.{u}, Encoding A T} (g : GeometricEncoding E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
        (E Y).ordinaryDerived.functor ≅
      (E X).ordinaryDerived.functor ⋙ directImageConstantPush A f := by
  let ET := (E Y).ordinary
  let EU := (E X).ordinary
  let F := CondensedRing.lowerStar (coefficient A) f
  let G := proEtaleConstantRingPushforward A f
  change F.rightDerivedFunctor ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (g.push f) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

/-- Descend the actual open adjunction comparison termwise.
Source: Stacks 015F, 03DI (blueprint: lem-pur-scalar-right-unit). -/
def geometricDerivedOpen {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    {E : ∀ T : Scheme.{u}, Encoding A T} (g : GeometricEncoding E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
        (E Y).ordinaryDerived.functor ≅
      (E X).ordinaryDerived.functor ⋙ (sfIntrinsicExtensionByZero j A).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (geometricOpen g j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The specified compactification comparison: the derived proper/direct-image
comparison followed by the exact open comparison for the same compactification.
Both factors were fixed by identity on sections and adjunction units.
Source: blueprint Proof (3), Tensor map; Stacks 015F, 03DI, 07A5
(blueprint: lem-pur-scalar-right-unit). -/
def geometricCompact {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    {E : ∀ T : Scheme.{u}, Encoding A T} (g : GeometricEncoding E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
        (E Y).ordinaryDerived.functor ≅
      (E X).ordinaryDerived.functor ⋙ reductionCompactSupport A c.i c.g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (geometricDerivedPush g c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (geometricDerivedOpen g c.i) _ ≪≫
    Functor.associator _ _ _

attribute [instance] Transport.arrowMon

end ScalarIdentification

/-- Right unitality of the specified, uncompleted pro-etale scalar extension,
including its representative and condensed/compact-support identifications.

Source: blueprint det-sp-reduction-compatibilities, Proof (3), Tensor map
(blueprint: lem-pur-scalar-right-unit).

Proof: restrict localization to flat-term K-flat representatives, where the
actual scalar computation counits and native tensor comparisons are invertible.
The balanced cochain tensor comparison descends through fully faithful
restriction. Its representative square and naturality at the chosen resolution
isomorphisms identify its components with precisely proEtaleScalarTensor.
This proves the prescribed tensor normalization; the unit normalization follows
by cancelling the target native unit isomorphism. Tensor closure of K-flatness
makes both concrete comparisons invertible.

Apply right-unit transport at a chosen representative and the coefficient unit.
The cochain comparison obeys the ordinary right-unit equation, and its normalized
localization squares give the desired equation after cancelling the computation
counit. Naturality transports the equation to every unbounded derived object.

Put the finite coefficient rings in their discrete topology. The normalized
ordinary/total/derived encoding identifies the same concrete comparisons with
the actual condensed tensor and unit maps. The compactification mate comparison
identifies the specified proper counit mate followed by open balancing. Append
the normalized condensed compact projection square for that same arrow and
compactification. No arbitrary comparison is substituted for a specified map,
and no flatness of B over A enters.
-/
theorem scalarRightUnit
    (ell : ℕ) [Fact ell.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
    (φ : A →+* B) (T : Scheme.{u}) :
    (∀ K : proEtaleDerivedCategory T A,
      proEtaleScalarTensor φ T K (𝟙_ _) ≫
          ((scalarExtensionFunctor φ T).obj K ◁ proEtaleScalarUnit φ T) ≫
            (ρ_ ((scalarExtensionFunctor φ T).obj K)).hom =
        (scalarExtensionFunctor φ T).map (ρ_ K).hom) ∧
    ProEtaleScalarTensorNormalized φ T ∧ ProEtaleScalarUnitNormalized φ T ∧
    (∀ K L : proEtaleDerivedCategory T A, IsIso (proEtaleScalarTensor φ T K L)) ∧
    IsIso (proEtaleScalarUnit φ T) ∧
    (letI : TopologicalSpace A := ⊥
     letI : TopologicalSpace B := ⊥
     letI : DiscreteTopology A := ⟨rfl⟩
     letI : DiscreteTopology B := ⟨rfl⟩
     ∃ d : ScalarIdentification.Transport φ,
       ScalarIdentification.CompactCompatible ell φ d) := by
  obtain ⟨⟨a, ha⟩, hn⟩ := proEtaleScalarTensor_natural_normalized φ T
  refine ⟨?_, hn, proEtaleScalarUnit_normalized φ T, ?_,
    proEtaleScalarUnit_isIso φ T, ?_⟩
  · intro K
    exact proEtaleScalarTensor_rightUnit_of_normalized φ T a ha hn K
  · intro K L
    exact proEtaleScalarTensor_isIso φ T K L
  · let : TopologicalSpace A := ⊥
    let : TopologicalSpace B := ⊥
    let : DiscreteTopology A := ⟨rfl⟩
    let : DiscreteTopology B := ⟨rfl⟩
    obtain ⟨d⟩ := ScalarIdentification.scalar_transport_exists (A := A) (B := B) φ
    exact ⟨d, ScalarIdentification.compactCompatible_of_mates ell φ d
      (ScalarIdentification.scalar_compactification_mates ell _hA _hB φ d)⟩

end AlgebraicGeometry.ProEtale
