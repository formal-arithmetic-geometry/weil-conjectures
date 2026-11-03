/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
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
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalAdjointAdmissibility
public import WeilConjectures.DeligneLaumon.NativeOpenExtension.NativeOpenCoefficientObjects
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
import WeilConjectures.PoincareDuality.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.AlgebraicGeometry.CondensedScalarExchangeCoherence

/-! # Condensed basic operations and coefficient reduction

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-verdier,
lem-fix-operation-reduction, statement and proof paragraphs 1--3.
(blueprint: lem-fix-operation-reduction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance] scalarSixChangeMonoidal

open WeilConjectures.NativeOpenExtension

/-- The actual quotient map of commutative condensed rings, at positive exponent n+1.
Source: blueprint lem-fix-operation-reduction, first displayed reduction; the
coefficient construction is sk-def-pe-derived-completion.
(blueprint: lem-fix-operation-reduction). -/
def basicOperationsIntegralReduction (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) :
    (⟨DerivedNakayama.integerRing ell E⟩ : ScalarSixRing.{u}) ⟶
      ⟨DerivedNakayama.quotientRing ell E (n + 1)⟩ :=
  letI : IsMonHom (DerivedNakayama.reductionRing ell E (n + 1)) :=
    Sheaf.isMonHom_sheafCompose_map _ (DerivedNakayama.reductionRingSheaf ell E (n + 1))
  CommMon.homMk (Mon.ofHom (DerivedNakayama.reductionRing ell E (n + 1)))

/-- Localization O_E to E in exactly the integral model used by reduction.
The map is continuous postcomposition with the inclusion of the valuation ring.
Source: blueprint lem-fix-operation-reduction, localization clause
(blueprint: lem-fix-operation-reduction). -/
def basicOperationsLocalization (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] :
    (⟨DerivedNakayama.integerRing ell E⟩ : ScalarSixRing.{u}) ⟶ ⟨fieldRing ell E⟩ :=
  letI : IsMonHom (inclusion ell E) :=
    Sheaf.isMonHom_sheafCompose_map _ (inclusionSheaf ell E)
  CommMon.homMk (Mon.ofHom (inclusion ell E))

/-- The native spectral absolute-value topology is a normed space over Q_ell.
The module structure is the given algebra structure and the norm bound is the
existing spectral algebra norm's scalar identity.
Source: blueprint coefficient convention (blueprint: lem-fix-operation-reduction). -/
@[instance_reducible]
def basicOperationsFieldNormedSpace (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] :
    letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
    NormedSpace (Padic ell) E :=
  letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
  { (inferInstance : Module (Padic ell) E) with
    norm_smul_le r x := by
      change spectralMulAlgNorm (Padic ell) E (r • x) ≤
        ‖r‖ * spectralMulAlgNorm (Padic ell) E x
      exact le_of_eq (map_smul_eq_mul _ _ _) }

/-- Continuous field scalar extension in the same spectral-topology model as localization.
Continuity is the existing finite-dimensional linear-map theorem; it is not an assumption.
Source: blueprint lem-fix-operation-reduction, E to F scalar extension
(blueprint: lem-fix-operation-reduction). -/
def basicOperationsFieldMapSheaf (ell : ℕ) [Fact ell.Prime]
    (E F : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    [Field F] [Algebra (Padic ell) F] [FiniteDimensional (Padic ell) F]
    (ι : E →ₐ[Padic ell] F) : fieldRingSheaf ell E ⟶ fieldRingSheaf ell F :=
  letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
  letI := (Padic.coefficientExtensionAbsoluteValue ell F).toNormedField
  letI : NormedSpace (Padic ell) E := basicOperationsFieldNormedSpace ell E
  letI : NormedSpace (Padic ell) F := basicOperationsFieldNormedSpace ell F
  fieldMapSheaf ell E F ι ι.toLinearMap.continuous_of_finiteDimensional

/-- The actual bundled map E to F, acting by postcomposition on continuous sections.
Source: blueprint lem-fix-operation-reduction, field extension clause
(blueprint: lem-fix-operation-reduction). -/
def basicOperationsFieldExtension (ell : ℕ) [Fact ell.Prime]
    (E F : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    [Field F] [Algebra (Padic ell) F] [FiniteDimensional (Padic ell) F]
    (ι : E →ₐ[Padic ell] F) :
    (⟨fieldRing ell E⟩ : ScalarSixRing.{u}) ⟶ ⟨fieldRing ell F⟩ :=
  let a := (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (basicOperationsFieldMapSheaf ell E F ι)
  letI : IsMonHom a := Sheaf.isMonHom_sheafCompose_map _
    (basicOperationsFieldMapSheaf ell E F ι)
  CommMon.homMk (Mon.ofHom a)

/-- Include native E-valued continuous sections in the finite-subextension-valued
algebraic-closure coefficients. Their values lie in the actual field range of ι,
which is finite dimensional since E is. Thus the target is Qlbar, not its completion.
Source: blueprint lem-fix-operation-reduction, F to Qlbar clause
(blueprint: lem-fix-operation-reduction). -/
def basicOperationsClosureMapSheaf (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (ι : E →ₐ[Padic ell] PadicAlgCl ell) :
    fieldRingSheaf ell E ⟶ Profinite.padicAlgClCondensedRing ell :=
  letI := (Padic.coefficientExtensionAbsoluteValue ell E).toNormedField
  letI : NormedSpace (Padic ell) E := basicOperationsFieldNormedSpace ell E
  ⟨{ app := fun P ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
       (((ι.toRingHom.compLeftContinuous P.unop
         ι.toLinearMap.continuous_of_finiteDimensional).codRestrict
           (PadicAlgCl.finiteIntermediateFieldValued ell P.unop)
           (fun s ↦ (PadicAlgCl.mem_finiteIntermediateFieldValued_iff ell _ _).mpr
             ⟨ι.fieldRange, ι.toLinearMap.finiteDimensional_range, fun x ↦ ⟨s x, rfl⟩⟩)).comp
               ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The canonical scalar map to the fixed algebraic closure on the native field model.
Source: blueprint lem-fix-operation-reduction, algebraic-closure extension
(blueprint: lem-fix-operation-reduction). -/
def basicOperationsClosureExtension (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (ι : E →ₐ[Padic ell] PadicAlgCl ell) :
    (⟨fieldRing ell E⟩ : ScalarSixRing.{u}) ⟶ ⟨Profinite.padicAlgClRingObj ell⟩ :=
  let a := (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (basicOperationsClosureMapSheaf ell E ι)
  letI : IsMonHom a := Sheaf.isMonHom_sheafCompose_map _
    (basicOperationsClosureMapSheaf ell E ι)
  CommMon.homMk (Mon.ofHom a)

end AlgebraicGeometry.ProEtale.CondensedRing
