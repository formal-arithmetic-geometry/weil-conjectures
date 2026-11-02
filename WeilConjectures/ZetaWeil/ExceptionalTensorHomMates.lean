/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
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

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StandingFieldCtfStability
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.ProjectionFormulaShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperExchangeComparison
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact

set_option linter.style.longLine false

/-!
# Condensed exceptional inverse image tensor--Hom and dualizing mates

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/_section.md`,
formulas (11.1)--(11.3), the evaluation and proper-bidual paragraphs, and the Complement.
(blueprint: lem-sf-exceptional-integral-left-scalar-mates).

## Main definitions

* `homExchangeMap`, `dualizingExchangeMap`, `pullbackDualizingExchangeMap`: the canonical mates.
* `condensedDualizingObject`, `constructibleDual`, `signedBidualMap`: omega, dual and delta.
* `properBidualComparisonMap`: the two-use proper dualizing comparison.

## Main statements

* `ExceptionalIntegralLeftScalarMates` collects invertibility and the required commuting squares.
* `exceptional_integral_left_scalar_mates` states the node with postponed proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.haveILetI false
set_option linter.defProp false

universe u

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open AlgebraicGeometry.ProEtale
open WeilConjectures
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The coefficient tensor unit, regarded in the constructible finite-Tor full subcategory.
Source: `sk-def-ops`, coefficient unit (blueprint: sk-thm-sf-tensor-hom). -/
def condensedCtfUnit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    ConstantModelConstructibleFiniteTor Λ T :=
  ⟨@MonoidalCategoryStruct.tensorUnit
    (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)))
    _ MonoidalCategory.toMonoidalCategoryStruct, condensedCoefficientUnit_mem Λ T⟩

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The constructible finite-Tor subcategory used throughout the six operations.
Source: `det-def-sf-operations` (blueprint: `det-def-sf-operations`). -/
abbrev Ctf (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  ConstantModelConstructibleFiniteTor Λ X

/-- The pullback object in the constructible finite-Tor full subcategory, using recorded stability.
Source: `det-thm-sf-ctf-stability-direct-images`, standing-field specialization
(blueprint: det-thm-sf-ctf-stability-direct-images). -/
noncomputable def ctfPullbackObject
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (L : Ctf Λ Y.left) :
    Ctf Λ X.left := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  letI : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  letI : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  letI : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  letI : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  letI : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  letI : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  exact ⟨(moduleObjectDerivedPullback Λ f.left).obj L.obj,
    (constructibleFiniteTor_stability_direct_images_of_finite_or_isAlgClosed
      ell k hk Λ hΛ f.left).1 L.obj L.property⟩

/-- The tensor object in the constructible finite-Tor full subcategory, using recorded stability.
Source: `det-thm-sf-ctf-stability-direct-images`, standing-field specialization
(blueprint: det-thm-sf-ctf-stability-direct-images). -/
noncomputable def ctfTensorObject
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (K : Ctf Λ X.left) (L : Ctf Λ Y.left) :
    Ctf Λ X.left := by
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  letI : f.left.IsOver (Spec (.of k)) := ⟨f.w⟩
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  letI : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  letI : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  letI : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  letI : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  letI : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  exact ⟨MonoidalCategoryStruct.tensorObj K.obj
      ((moduleObjectDerivedPullback Λ f.left).obj L.obj),
    (constructibleFiniteTor_stability_direct_images_of_finite_or_isAlgClosed
      ell k hk Λ hΛ f.left).2.1 K.obj
        ((moduleObjectDerivedPullback Λ f.left).obj L.obj) K.property
        (ctfPullbackObject ell k hk Λ hΛ f L).property⟩

/-- The compact-support exceptional projection component on the stated finite-Tor objects.
Source: `det-def-sf-operations`, projection formula clause (blueprint: sk-thm-sf-tensor-hom). -/
noncomputable def exceptionalProjectionApp
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (K : Ctf Λ X.left) (L : Ctf Λ Y.left) :
    MonoidalCategoryStruct.tensorObj
      ((ctfLowerShriek Λ ell k (exceptionalCurrentFieldCD ell k hk) f hΛ).obj K).obj L.obj ⟶
      ((ctfLowerShriek Λ ell k (exceptionalCurrentFieldCD ell k hk) f hΛ).obj
        ⟨MonoidalCategoryStruct.tensorObj K.obj
          ((moduleObjectDerivedPullback Λ f.left).obj L.obj),
          (ctfTensorObject ell k hk Λ hΛ f K L).property⟩).obj := by
  let hcd := exceptionalCurrentFieldCD ell k hk
  exact exceptionalProjectionMorphismOfCompactification Λ
    (compactificationOverField f) K.obj L.obj

/-- The restricted exceptional projection map at a constructible pair.
Source: `det-def-sf-operations`, projection formula clause (blueprint: sk-thm-sf-tensor-hom). -/
noncomputable def homProjectionApp
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (K : Ctf Λ X.left) (L : Ctf Λ Y.left) :=
  exceptionalProjectionApp ell k hk Λ hΛ f K (ctfHomInput ell k hk Λ hΛ f K L)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

/-- The single evaluation morphism used by both sides of every mate.  It is the counit of the
relative derived tensor--Hom adjunction, and hence carries the Koszul sign convention.  Source:
`det-def-sfb-derived-tensor-hom`, derived tensor--Hom adjunction
(blueprint: sk-thm-sf-tensor-hom). -/
noncomputable def evaluationMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme} (P K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    ((RHom(X)⟦Λ⟧).obj (op P) ⋙
      (-⊗ᴸ-(X)⟦Λ⟧.obj P)).obj K ⟶ (𝟭 _).obj K :=
  (derivedTensorHomAdjunction Λ P).counit.app K

/-- The signed bidual arrow, obtained by transposing evaluation after the tensor symmetry.
Source: `sk-thm-pd-verdier-duality`, definition of the signed bidual
(blueprint: sk-thm-pd-verdier-duality). -/
noncomputable def signedBidualMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme} (M ω : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    M ⟶ ((RHom(X)⟦Λ⟧).obj (op (((RHom(X)⟦Λ⟧).obj (op M)).obj ω))).obj ω := by
  let N := ((RHom(X)⟦Λ⟧).obj (op M)).obj ω
  let ev : MonoidalCategoryStruct.tensorObj M N ⟶ ω :=
    (derivedTensorHomAdjunction Λ M).counit.app ω
  exact (derivedTensorHomAdjunction Λ N).homEquiv M ω
    ((@BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) N M).hom ≫ ev)

/-- Proper exchange for the compact-support formalism used by the composition mate.
Source: `det-prop-sf-cbc`, proper-exchange clause (blueprint: sk-thm-sf-tensor-hom).
Proof: proper base change gives invertibility of proper exchange; its identity and
pasting laws identify the exchange map of the compact-support formalism with that
published canonical map. -/
theorem compactSupportCondensedFormalism_hasProperExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    (AlgebraicGeometry.ProEtale.CondensedRing.compactSupportCondensedFormalism Λ
      ).HasProperExchange := by
  sorry

attribute [local irreducible] condensedDualizingObject condensedCtfUnit
  AlgebraicGeometry.ProEtale.CondensedRing.ctfExceptionalInverseImage
  AlgebraicGeometry.ProEtale.CondensedRing.ctfExceptionalAdjunction

set_option maxHeartbeats 800000 in
-- Nested adjunction transposes require conversions between full subcategories
-- and their ambient categories.
/-- The dualizing specialization of the canonical Hom mate.
Source: `sk-thm-sf-tensor-hom`, formula (11.2) (blueprint: sk-thm-sf-tensor-hom). -/
noncomputable def dualizingExchangeMap
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (K : Ctf Λ X.left)
    (hp : IsIso (homProjectionApp ell k hk Λ hΛ f K
      (condensedDualizingObject ell k hk Λ hΛ Y))) :
    ((RHom(Y.left)⟦Λ⟧).obj (op
      ((ctfLowerShriek Λ ell k (exceptionalCurrentFieldCD ell k hk) f hΛ).obj K).obj)).obj
        (condensedDualizingObject ell k hk Λ hΛ Y).obj ⟶
      (moduleObjectDerivedPushforward Λ f.left).obj
        (((RHom(X.left)⟦Λ⟧).obj (op K.obj)).obj
          (condensedDualizingObject ell k hk Λ hΛ X).obj) := by
  let h := homExchangeMap ell k hk Λ hΛ f K
    (condensedDualizingObject ell k hk Λ hΛ Y) hp
  let γ := dualizingCompositionMap ell k hk Λ hΛ f
  exact h ≫ (moduleObjectDerivedPushforward Λ f.left).map
    (((RHom(X.left)⟦Λ⟧).obj (op K.obj)).map γ)

/-- Clause (2) is invertible by the tensor--Hom mate theorem on constructible objects.
Source: formula (11.2), `sk-thm-sf-tensor-hom` (blueprint: sk-thm-sf-tensor-hom).
Proof: apply (11.1) with L = omega_Y, then the composition isomorphism
f^!omega_Y = omega_X. Both arrows are isomorphisms. -/
theorem dualizingExchangeMap_isIso
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (K : Ctf Λ X.left)
    (hp : IsIso (homProjectionApp ell k hk Λ hΛ f K
      (condensedDualizingObject ell k hk Λ hΛ Y))) :
    IsIso (dualizingExchangeMap ell k hk Λ hΛ f K hp) := by
  sorry

/-- The exceptional projection component is invertible on constructible finite-Tor inputs.
Source: `sk-thm-sf-tensor-hom`, proof paragraph invoking the exceptional projection
formula (blueprint: sk-thm-sf-tensor-hom).
Proof: compactify f; the open-immersion projection formula and the proper projection
formula are isomorphisms on constructible finite-Tor inputs. Their composite is the
published exceptional projection morphism. -/
theorem exceptionalProjectionApp_isIso
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (K : Ctf Λ X.left) (L : Ctf Λ Y.left) :
    IsIso (exceptionalProjectionApp ell k hk Λ hΛ f K L) := by
  sorry

/-- The proper compact-support comparison used in the bidual mate.
Source: proper compact-support/direct-image comparison in `det-prop-sf-cbc`;
proof step: compare the specified compactification with `Compactification.ofIsProper`.
(blueprint: sk-thm-sf-tensor-hom).
-/
noncomputable def properLowerShriekToStarIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f) ≅
      moduleObjectDerivedPushforward Λ f.left := by
  let F := compactSupportCondensedFormalism Λ
  letI : F.HasProperExchange := compactSupportCondensedFormalism_hasProperExchange Λ
  exact F.shriekIso (compactificationOverField f) (Compactification.ofIsProper f.left) ≪≫
    properIdentityComparison Λ f.left

set_option maxHeartbeats 800000 in
-- Nested adjunction transposes require conversions between full subcategories
-- and their ambient categories.
/-- The evaluation square for (11.1), expressed after the ordinary and closed transposes.
Source: `sk-thm-sf-tensor-hom`, evaluation paragraph
(blueprint: sk-thm-sf-tensor-hom).
Proof: undo the two final transposes of homExchangeMap, apply the exceptional counit,
and precompose with projection. The exceptional triangle identity leaves exactly
the tensor-Hom evaluation on Y. -/
theorem homExchange_preserves_evaluation
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (K : Ctf Λ X.left) (L : Ctf Λ Y.left)
    (hp : IsIso (homProjectionApp ell k hk Λ hΛ f K L)) :
    let hcd := exceptionalCurrentFieldCD ell k hk
    let P := ctfLowerShriek Λ ell k hcd f hΛ
    let S := ctfExceptionalInverseImage Λ ell k hcd f hΛ
    let A := ctfHomInput ell k hk Λ hΛ f K L
    let T : Ctf Λ X.left :=
      ⟨MonoidalCategoryStruct.tensorObj K.obj
          ((moduleObjectDerivedPullback Λ f.left).obj A.obj),
        (ctfTensorObject ell k hk Λ hΛ f K A).property⟩
    let h := homExchangeMap ell k hk Λ hΛ f K L hp
    let t := ((derivedTensorHomAdjunction Λ K.obj).homEquiv
      ((moduleObjectDerivedPullback Λ f.left).obj A.obj) (S.obj L).obj).symm
        (((derivedUpperStarLowerStarAdjunction Λ f.left).homEquiv A.obj
          (((RHom(X.left)⟦Λ⟧).obj (op K.obj)).obj (S.obj L).obj)).symm h)
    homProjectionApp ell k hk Λ hΛ f K L ≫
        (P.map (show T ⟶ S.obj L from ObjectProperty.homMk t)).hom ≫
        ((ctfExceptionalAdjunction Λ ell k hcd f hΛ).counit.app L).hom =
      evaluationMap Λ (P.obj K).obj L.obj := by
  sorry

/-- The two naturality squares of the canonical mate, contravariant in K and covariant in L.
Source: `sk-thm-sf-tensor-hom`, Complement (blueprint: sk-thm-sf-tensor-hom).
Proof: naturality of projection, evaluation, all three adjunction bijections and both
counits gives the L square and the K square separately. -/
theorem homExchange_natural_in_K_L
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left]
    [QuasiCompact f.left] (K' K : Ctf Λ X.left) (L L' : Ctf Λ Y.left)
    (a : K' ⟶ K) (b : L ⟶ L')
    (hp : IsIso (homProjectionApp ell k hk Λ hΛ f K L))
    (hp₁ : IsIso (homProjectionApp ell k hk Λ hΛ f K L'))
    (hp₂ : IsIso (homProjectionApp ell k hk Λ hΛ f K' L))
    (hp' : IsIso (homProjectionApp ell k hk Λ hΛ f K' L')) :
    ((RHom(Y.left)⟦Λ⟧).obj (op
      ((ctfLowerShriek Λ ell k (exceptionalCurrentFieldCD ell k hk) f hΛ).obj K).obj)).map b.hom ≫
      homExchangeMap ell k hk Λ hΛ f K L' hp₁ =
    homExchangeMap ell k hk Λ hΛ f K L hp ≫
      (moduleObjectDerivedPushforward Λ f.left).map
        (((RHom(X.left)⟦Λ⟧).obj (op K.obj)).map
          ((ctfExceptionalInverseImage Λ ell k
            (exceptionalCurrentFieldCD ell k hk) f hΛ).map b).hom) ∧
    ((RHom(Y.left)⟦Λ⟧).map
      (((ctfLowerShriek Λ ell k
        (exceptionalCurrentFieldCD ell k hk) f hΛ).map a).hom.op)).app L.obj ≫
        homExchangeMap ell k hk Λ hΛ f K' L hp₂ =
      homExchangeMap ell k hk Λ hΛ f K L hp ≫
        (moduleObjectDerivedPushforward Λ f.left).map
          (((RHom(X.left)⟦Λ⟧).map a.hom.op).app
            ((ctfExceptionalInverseImage Λ ell k
            (exceptionalCurrentFieldCD ell k hk) f hΛ).obj L).obj) := by
  sorry

end WeilConjectures
