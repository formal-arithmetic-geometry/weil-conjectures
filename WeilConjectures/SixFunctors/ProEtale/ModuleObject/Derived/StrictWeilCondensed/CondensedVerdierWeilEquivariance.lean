/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.BaseChange
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
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.CategoryTheory.WeilEquivariance
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedArbitraryPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs

/-! # Weil equivariance of duality on the current condensed strict Weil model

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-def-ops/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.md and .proof.md
(blueprint: cor-coef-verdier-weil-equivariance).

Proof steps: (1) restrict the operations and use the canonical compact-support exchange and
its exceptional mate to form w = a_X^!(tau_0) b_a; (2) apply the monoidal internal-Hom
comparison to theta inverse and w, and use its naturality; (3) evaluation and its symmetric
transpose give equivariance of evaluation and the invertible canonical biduality map;
(4) the normalized scalar pullback, exceptional and evaluation mates intertwine these same
structures, giving the scalar dualizing, dual and biduality comparisons and both original
exceptional-adjunction maps. No integral lattice is used.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed

/-- Separatedness of the actual geometric fibre. Source: the standing model hypotheses
(blueprint: cor-coef-verdier-weil-equivariance). -/
instance verdierFiberSeparated (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    IsSeparated (D.geometricFiber T₀).hom := by
  dsimp [WeilConjectures.FiniteFieldDatum.geometricFiber]
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The characteristic hypothesis on the fixed algebraic closure. Source: ell != p
(blueprint: cor-coef-verdier-weil-equivariance). -/
instance verdierClosureCharDifferent (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D.p)] : Fact (ringChar D.k ≠ ell) := by
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let _ : Fact D.p.Prime := ⟨D.prime⟩
  let _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let _ : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ⟨by rw [ringChar.eq D.k D.p]; exact (Fact.out : ell ≠ D.p).symm⟩

/-- Finite type of the actual geometric fibre. Source: the standing model hypotheses
(blueprint: cor-coef-verdier-weil-equivariance). -/
instance verdierFiberLft (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    LocallyOfFiniteType (D.geometricFiber T₀).hom :=
  WeilConjectures.FrobeniusExchange.fiberLocallyFiniteType D T₀

/-- Quasi-compactness of the actual geometric fibre. Source: the standing model hypotheses
(blueprint: cor-coef-verdier-weil-equivariance). -/
instance verdierFiberQc (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    QuasiCompact (D.geometricFiber T₀).hom :=
  WeilConjectures.FrobeniusExchange.fiberQuasiCompact D T₀

/-- The actual geometric base-change morphism, retaining its Over type.
Source: the descended f of proof Step 1 (blueprint: cor-coef-verdier-weil-equivariance). -/
def verdierFiberMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    D.geometricFiber X₀ ⟶ D.geometricFiber Y₀ :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀

/-- The component of the normalized proper/open exchange.  Its data are the
explicit square exchange and normalized compactification comparison.
Source: proof Step 1, e_f component (blueprint: cor-coef-verdier-weil-equivariance). -/
def canonicalSupportExchangeComponent (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ell ≠ D.p)]
    (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (g : X.left ≅ X.left) (h : Y.left ≅ Y.left)
    (c' : Compactification f.left)
    (B : CompactificationReindexing.F Λ.X (compactificationOverField f) ⋙
        CompactificationReindexing.P Λ.X h.hom ≅
      CompactificationReindexing.P Λ.X g.hom ⋙
        CompactificationReindexing.F Λ.X c')
    (τ : (localizingClosureProEtale Λ.X X.left).ι ⋙
        detSfCompactSupport Λ.X c' ≅
      (localizingClosureProEtale Λ.X X.left).ι ⋙
        detSfCompactSupport Λ.X (compactificationOverField f))
    (A : SixOperationsLocalizingAdjunction Λ.X (compactificationOverField f))
    (hg : UnboundedLocalizingPullback Λ.X g.hom)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    (ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ ⋙
        smallAction Λ.X h).obj K ≅
      (smallAction Λ.X g ⋙
        ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ).obj K := by
  let c := compactificationOverField f
  let LK : (localizingClosureProEtale Λ.X X.left).FullSubcategory :=
    ⟨K.obj, A.source_mem K.obj K.property⟩
  let LgK : (localizingClosureProEtale Λ.X X.left).FullSubcategory :=
    ⟨(CompactificationReindexing.P Λ.X g.hom).obj K.obj, by
      simpa [LK, CompactificationReindexing.P] using hg.localizing LK⟩
  let qτ := τ.app LgK
  let q₀ := ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X h.hom).app
    ((CompactificationReindexing.F Λ.X c).obj K.obj)).symm
  let q₁ := B.app K.obj
  let q₂ := (CompactificationReindexing.F Λ.X c).mapIso
    ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X g.hom).app K.obj)
  let q := q₀ ≪≫ q₁ ≪≫ qτ ≪≫ q₂
  let q' : ((ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ ⋙
      smallAction Λ.X h).obj K).obj ⟶
      ((smallAction Λ.X g ⋙
        ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ).obj K).obj := by
    simpa [ctfLowerShriek, smallAction] using q.hom
  let qinv' : ((smallAction Λ.X g ⋙
        ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ).obj K).obj ⟶
      ((ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ ⋙
        smallAction Λ.X h).obj K).obj := by
    simpa [ctfLowerShriek, smallAction] using q.inv
  exact {
    hom := ObjectProperty.homMk q'
    inv := ObjectProperty.homMk qinv'
    hom_inv_id := by apply ObjectProperty.hom_ext; simp [q', qinv', q]
    inv_hom_id := by apply ObjectProperty.hom_ext; simp [q', qinv', q] }

/-- Naturality of the explicit square-exchange component.  This is the named
well-definedness proof used to lift the ambient composite along the fully faithful
full-subcategory inclusion.
Source: proof Step 1, naturality of e_f (blueprint: cor-coef-verdier-weil-equivariance). -/
theorem canonicalSupportExchangeComponent_naturality (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ell ≠ D.p)]
    (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (g : X.left ≅ X.left) (h : Y.left ≅ Y.left)
    (c' : Compactification f.left)
    (B : CompactificationReindexing.F Λ.X (compactificationOverField f) ⋙
        CompactificationReindexing.P Λ.X h.hom ≅
      CompactificationReindexing.P Λ.X g.hom ⋙
        CompactificationReindexing.F Λ.X c')
    (τ : (localizingClosureProEtale Λ.X X.left).ι ⋙
        detSfCompactSupport Λ.X c' ≅
      (localizingClosureProEtale Λ.X X.left).ι ⋙
        detSfCompactSupport Λ.X (compactificationOverField f))
    (A : SixOperationsLocalizingAdjunction Λ.X (compactificationOverField f))
    (hg : UnboundedLocalizingPullback Λ.X g.hom) :
    ∀ (K L : ConstantModelConstructibleFiniteTor Λ.X X.left) (fKL : K ⟶ L),
      (ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ ⋙
          smallAction Λ.X h).map fKL ≫
          (canonicalSupportExchangeComponent ell D Λ hΛ f g h c' B τ A hg L).hom =
        (canonicalSupportExchangeComponent ell D Λ hΛ f g h c' B τ A hg K).hom ≫
          (smallAction Λ.X g ⋙
            ctfLowerShriek Λ.X ell D.k
              (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ).map fKL := by
  sorry

/-- The normalized proper/open exchange in exact Frobenius-action coordinates.
It is the explicit composite of the native `squareExchange` on the transported
compactification with the normalized compactification comparison.
Source: proof Step 1, e_f (blueprint: cor-coef-verdier-weil-equivariance). -/
def canonicalSupportExchange (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ell ≠ D.p)]
    (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (_hField : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (g : X.left ≅ X.left) (h : Y.left ≅ Y.left)
    (sq : IsPullback g.hom f.left f.left h.hom) :
    ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ ⋙
        smallAction Λ.X h ≅
      smallAction Λ.X g ⋙
        ctfLowerShriek Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ := by
  let c := compactificationOverField f
  let c' : Compactification f.left := {
    Z := c.Z
    i := g.hom ≫ c.i
    g := c.g ≫ h.inv
    comm := by
      change f.left = (g.hom ≫ c.i) ≫ (c.g ≫ h.inv)
      calc
        f.left = f.left ≫ h.hom ≫ h.inv := by simp
        _ = g.hom ≫ f.left ≫ h.inv := by
          calc
            f.left ≫ h.hom ≫ h.inv = (f.left ≫ h.hom) ≫ h.inv := by simp
            _ = (g.hom ≫ f.left) ≫ h.inv := by rw [sq.w.symm]
            _ = g.hom ≫ f.left ≫ h.inv := by simp
        _ = g.hom ≫ c.i ≫ c.g ≫ h.inv := by
          have hc : f.left = c.i ≫ c.g := c.comm
          simpa only [Category.assoc] using
            congrArg (fun k : X.left ⟶ Y.left ↦ g.hom ≫ k ≫ h.inv) hc
    isProper := inferInstance
    isOpenImmersion := inferInstance }
  let s : CompactificationReindexing.Square c c' g.hom h.hom := {
    middle := 𝟙 c.Z
    openSquare := by
      let : IsIso (𝟙 c.Z) := IsIso.id c.Z
      exact IsPullback.of_horiz_isIso (fst := g.hom) (snd := c'.i)
        (f := c.i) (g := 𝟙 c.Z) ⟨by simp [c']⟩
    properSquare := ⟨by
      change (𝟙 c.Z) ≫ c.g = (c.g ≫ h.inv) ≫ h.hom
      simp⟩ }
  have hB : IsIso (CompactificationReindexing.squareExchange Λ.X s) := by
    exact (CompactificationReindexing.square_isIso Λ.X s sq.toCommSq).2
  let B : CompactificationReindexing.F Λ.X c ⋙
      CompactificationReindexing.P Λ.X h.hom ≅
    CompactificationReindexing.P Λ.X g.hom ⋙
      CompactificationReindexing.F Λ.X c' := asIso
        (CompactificationReindexing.squareExchange Λ.X s)
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (LocallyOfFiniteType X.hom)
  letI : QuasiCompact (X.left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (QuasiCompact X.hom)
  letI : IsSeparated (X.left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (IsSeparated X.hom)
  letI : LocallyOfFiniteType (Y.left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (LocallyOfFiniteType Y.hom)
  letI : QuasiCompact (Y.left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (QuasiCompact Y.hom)
  letI : IsSeparated (Y.left ↘ Spec (.of D.k)) := by
    exact inferInstanceAs (IsSeparated Y.hom)
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  letI : Fact (ringChar D.k ≠ ell) := ⟨by
    rw [ringChar.eq D.k D.p]
    exact (Fact.out : ell ≠ D.p).symm⟩
  let hAdm : IsAdmissibleCoefficient Λ.X := by
    rcases _hField with ⟨⟨E, hE⟩⟩ | hq
    · exact ⟨ell, inferInstance, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩))))⟩
    · exact ⟨ell, inferInstance, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq))))⟩
  have hEll : D.p ≠ ell := (Fact.out : ell ≠ D.p).symm
  let hg : UnboundedLocalizingPullback Λ.X g.hom :=
    (condensedArbitraryPullback D.p ell hEll D.k Λ.X hAdm g.hom).2.1
  let A := sixOperationsLocalizingAdjunction Λ.X ell D.k
    (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ
  letI : IsSeparated (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  letI : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  letI : QuasiCompact (f.left ≫ Y.hom) := by rw [Over.w f]; infer_instance
  letI : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  letI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  letI : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  let τ := detSfCanonicalCompactificationComparison Λ.X ell hΛ D.k f.left c' c
  exact NatIso.ofComponents
    (canonicalSupportExchangeComponent ell D Λ hΛ f g h c' B τ A hg)
    (fun {K L} fKL =>
      canonicalSupportExchangeComponent_naturality ell D Λ hΛ f g h c' B τ A hg K L fKL)

/-- The canonical mate b_f of inverse e_f, with the original exceptional adjunction.
Source: proof Step 1 (blueprint: cor-coef-verdier-weil-equivariance). -/
def canonicalExceptionalExchange (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ell ≠ D.p)]
    (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (hField : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    {X Y : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (g : X.left ≅ X.left) (h : Y.left ≅ Y.left)
    (sq : IsPullback g.hom f.left f.left h.hom) :=
  Adjunction.rightAdjointExchange
    (ctfExceptionalAdjunction Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ)
    (ctfExceptionalAdjunction Λ.X ell D.k (BaseFieldFiniteCD.of_isAlgClosed ell D.k) f hΛ)
    (canonicalSupportExchange ell D Λ hΛ hField f g h sq)

/-- The exact pullback commuting square, built from compositor, scheme equality, compositor.
Source: proof Step 4, pullback comparison (blueprint:
sk-thm-sf-package/cor-coef-verdier-weil-equivariance). -/
def canonicalPullWeilExchange (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : X ≅ X) (h : Y ≅ Y) (sq : CommSq g.hom f f h.hom) :
    action Λ.X h ⋙ scalarSixPull Λ f ≅ scalarSixPull Λ f ⋙ action Λ.X g :=
  (scalarSixPullComp Λ f h.hom).symm ≪≫
    eqToIso (congrArg (scalarSixPull Λ) sq.w.symm) ≪≫ scalarSixPullComp Λ g.hom f

end AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed
