/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import Mathlib.Tactic.DefEqTransformations
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
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
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import Mathlib.Lean.Meta.CongrTheorems
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComp
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedOpenRestrictedCounit

/-! # Integral projection system coordinates

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md,
compactification-independence sentence; integral-system realization steps 1 and 3 of
lem-sf-integral-projection-refinement-square.
(blueprint: lem-sf-integral-projection-system-coordinates).

The native coordinates in the two comparison cases are recorded here; the
compatibility proof is postponed to the proof node. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The alpha refinement equation of case (1),
alpha_c R_Y(r_(r,K) tensor 1) = (r_(r',R_X K) tensor 1) alpha_d, with the native
tensorator and exchange.
Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md, compactification-independence sentence;
the refinement exchange of
lem-fix-condensed-compactification-reindexing.
(blueprint: lem-sf-integral-projection-system-coordinates). -/
abbrev integralAlphaRefinementCoordinate
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (v : Y' ⟶ Y) [IsIso v]
    (K : CompactificationReindexing.D Λ X)
    (L : CompactificationReindexing.D Λ Y) : Prop :=
  let αc :=
    ((leftDerivedUpperStarTensor Λ v).app
      ((CompactificationReindexing.F Λ c).obj K)).app L ≫
      ((CompactificationReindexing.exchange Λ c v).app K ⊗ₘ 𝟙 _)
  let αd :=
    ((leftDerivedUpperStarTensor Λ v).app
      ((CompactificationReindexing.F Λ d).obj K)).app L ≫
      ((CompactificationReindexing.exchange Λ d v).app K ⊗ₘ 𝟙 _)
  (CompactificationReindexing.P Λ v).map
      ((CompactificationReindexing.refinement Λ r).app K ⊗ₘ 𝟙 _) ≫ αc =
    αd ≫
      ((CompactificationReindexing.refinement Λ
        (CompactificationReindexing.refinementBaseChange r v)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K) ⊗ₘ 𝟙 _)

/-- The beta refinement equation of case (1),
beta_c R_Y(r_(r,H)) = r_(r',H') beta_d, with the native tensor input.
Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md, compactification-independence sentence;
the refinement exchange of
lem-fix-condensed-compactification-reindexing.
(blueprint: lem-sf-integral-projection-system-coordinates). -/
abbrev integralBetaRefinementCoordinate
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) (v : Y' ⟶ Y) [IsIso v]
    (K : CompactificationReindexing.D Λ X)
    (L : CompactificationReindexing.D Λ Y) : Prop :=
  let H := K ⊗ (CompactificationReindexing.P Λ f).obj L
  let βc :=
    (CompactificationReindexing.exchange Λ c v).app H ≫
      (CompactificationReindexing.F Λ (c.baseChange v)).map
        (CompactificationReindexing.tensorInput Λ v K L)
  let βd :=
    (CompactificationReindexing.exchange Λ d v).app H ≫
      (CompactificationReindexing.F Λ (d.baseChange v)).map
        (CompactificationReindexing.tensorInput Λ v K L)
  (CompactificationReindexing.P Λ v).map
      ((CompactificationReindexing.refinement Λ r).app H) ≫ βc =
    βd ≫
      (CompactificationReindexing.refinement Λ
        (CompactificationReindexing.refinementBaseChange r v)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K ⊗
          (CompactificationReindexing.P Λ (pullback.snd f v)).obj
            ((CompactificationReindexing.P Λ v).obj L))

private def transportConversionAliases : Array Name := #[
  `inferInstance, `CochainComplex,
  `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensorLeft,
  `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensorRight,
  `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.D,
  `AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing.D,
  `AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing.P,
  `AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing.R,
  `AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing.J,
  `AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing.F,
  `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.refinementOpen,
  `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.L,
  `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.R,
  `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.J,
  `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.C,
  `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.compactTransport,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback,
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward,
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification,
  `CategoryTheory.Abelian.toPreadditive,
  `CategoryTheory.Mod.instAbelian, `CategoryTheory.Abelian.ofCoimageImageComparisonIsIso]

private def reduceTransportFunctorStep (fuel : Nat) (e : Expr) : MetaM Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let args := e.getAppArgs
    let n := e.getAppFn.constName?
    if let some v ← delta? e (fun n =>
        n == ``CompactificationReindexing.F || n == ``CompactificationReindexing.P ||
        n == ``CompactificationReindexing.R || n == ``CompactificationReindexing.J ||
        n == ``rightDerivedLowerShriekOfCompactification) then
      return ← reduceTransportFunctorStep fuel v.headBeta
    if n == some ``CategoryTheory.Functor.comp && args.size ≥ 2 then
      let i := args.size - 2
      let f ← reduceTransportFunctorStep fuel args[i]!
      let g ← reduceTransportFunctorStep fuel args[i + 1]!
      if f.getAppFn.isConstOf ``CategoryTheory.Functor.comp then
        let fs := f.getAppArgs
        let a := fs[fs.size - 2]!
        let b := fs[fs.size - 1]!
        let bg ← mkAppM ``CategoryTheory.Functor.comp #[b,g]
        return ← mkAppM ``CategoryTheory.Functor.comp #[a,bg]
      return mkAppN e.getAppFn ((args.set! i f).set! (i + 1) g)
    if (n == some ``CategoryTheory.Functor.obj || n == some ``CategoryTheory.Functor.map) &&
        args.size > 4 then
      let mut f ← reduceTransportFunctorStep fuel args[4]!
      for _ in [:8] do
        match ← delta? f (fun n => n == ``CategoryTheory.Functor.comp ||
            n == ``CategoryTheory.Functor.id ||
            n == ``CategoryTheory.Functor.whiskeringRight ||
            n == ``CategoryTheory.Functor.whiskeringLeft ||
            n == ``CategoryTheory.Functor.whiskeringLeft₂ ||
            n == ``CategoryTheory.MonoidalCategory.curriedTensor ||
            n == ``leftDerivedUpperStarTensorLeft ||
            n == ``leftDerivedUpperStarTensorRight ||
            n == `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.bc ||
            n == ``CategoryTheory.ObjectProperty.ι || n == ``CategoryTheory.inducedFunctor ||
            n == `AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport.C ||
            n ==
              `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification ||
            n == `AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing.F) with
        | some g => f ← reduceTransportFunctorStep fuel g.headBeta
        | none => break
      if f.getAppFn.isConstOf ``CategoryTheory.Functor.mk then
        let i := if n == some ``CategoryTheory.Functor.obj then 4 else 5
        return (mkAppN f.getAppArgs[i]! (args.extract 5 args.size)).headBeta
      return mkAppN e.getAppFn (args.set! 4 f)
    if n == some ``CategoryTheory.NatTrans.app && args.size ≥ 2 then
      let α := args[args.size - 2]!
      let K := args[args.size - 1]!
      let xs := α.getAppArgs
      if α.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && xs.size ≥ 2 then
        let a ← mkAppM ``CategoryTheory.NatTrans.app #[xs[xs.size - 2]!, K]
        let b ← mkAppM ``CategoryTheory.NatTrans.app #[xs[xs.size - 1]!, K]
        return ← mkAppM ``CategoryTheory.CategoryStruct.comp #[a,b]
      if α.getAppFn.isConstOf ``CategoryTheory.Functor.whiskerRight && xs.size ≥ 2 then
        let a ← mkAppM ``CategoryTheory.NatTrans.app #[xs[xs.size - 2]!, K]
        return ← mkAppM ``CategoryTheory.Functor.map #[xs[xs.size - 1]!, a]
      if α.getAppFn.isConstOf ``CategoryTheory.Functor.whiskerLeft && xs.size ≥ 4 then
        let K' ← mkAppM ``CategoryTheory.Functor.obj #[xs[xs.size - 4]!, K]
        return ← mkAppM ``CategoryTheory.NatTrans.app #[xs[xs.size - 1]!, K']
    return e

private def reduceTransportFunctor (e : Expr) : MetaM Expr := do
  let mut out := e
  for _ in [:16] do
    let next ← reduceTransportFunctorStep 64 out
    if next == out then break
    out := next
  return out

private def transportIdentityReduction? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let args := e.getAppArgs
  if e.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp && args.size ≥ 2 then
    let f := args[args.size - 2]!
    let g := args[args.size - 1]!
    if f.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.id then
      let h ← mkAppM ``CategoryTheory.Category.id_comp #[g]
      return some (g, ← mkAppM ``heq_of_eq #[h])
    if g.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.id then
      let h ← mkAppM ``CategoryTheory.Category.comp_id #[f]
      return some (f, ← mkAppM ``heq_of_eq #[h])
  return none

private structure TransportConversionState where
  proofs : Std.HashMap (Expr × Expr) Expr := {}
  congruences : Std.HashMap (Expr × Array Bool) CongrTheorem := {}

private def transportMetadataHEq (fuel : Nat) (left right : Expr) :
    StateRefT TransportConversionState MetaM Expr := do
  match fuel with
  | 0 => throwError "structural conversion exceeded its depth bound"
  | fuel + 1 =>
    let a ← reduceTransportFunctor left.consumeMData
    let b ← reduceTransportFunctor right.consumeMData
    if let some p := (← get).proofs.get? (a,b) then return p
    let p ← do
      if a == b then return ← mkHEqRefl a
      if (← isProof a) && (← isProof b) then
        return ← mkAppM ``proof_irrel_heq #[a,b]
      if let some (a', h) ← transportIdentityReduction? a then
        let h' ← transportMetadataHEq fuel a' b
        return ← mkAppM ``HEq.trans #[h,h']
      if let some (b', h) ← transportIdentityReduction? b then
        let h' ← transportMetadataHEq fuel a b'
        let hs ← mkAppM ``HEq.symm #[h]
        return ← mkAppM ``HEq.trans #[h',hs]
      let fa := a.getAppFn
      let fb := b.getAppFn
      let aa := a.getAppArgs
      let bb := b.getAppArgs
      if fa == fb && aa.size == bb.size && !aa.isEmpty then
        let info ← getFunInfoNArgs fa aa.size
        let fixed := aa.zip bb |>.map fun (x,y) => x == y
        let key := (fa,fixed)
        let thm ← match (← get).congruences.get? key with
          | some thm => pure thm
          | none => do
            let thm ← mkRichHCongr (← inferType fa) info
              (fixedFun := true) (fixedParams := fixed) (forceHEq := true)
            modify fun st => { st with congruences := st.congruences.insert key thm }
            pure thm
        let mut result := mkApp thm.proof fa
        for i in [:aa.size] do
          result := mkApp result aa[i]!
          match thm.argKinds[i+1]! with
          | .fixed => pure ()
          | .subsingletonInst => result := mkApp result bb[i]!
          | .eq | .heq =>
            result := mkApp result bb[i]!
            let expected ← whnf (← inferType result)
            let hp ← forallTelescope expected.bindingDomain! fun xs ty => do
              let hp ← match ty.eq?, ty.heq? with
                | some (_, x,y), _ => do
                  let h ← try transportMetadataHEq fuel x y catch ex =>
                    throwError "argument {i} of {fa.constName?}: {ex.toMessageData}"
                  mkAppM ``eq_of_heq #[h]
                | _, some (_, x, _, y) =>
                  try transportMetadataHEq fuel x y catch ex =>
                    throwError "argument {i} of {fa.constName?}: {ex.toMessageData}"
                | _, _ => throwError "unexpected congruence premise {ty}"
              mkLambdaFVars xs hp
            result := mkApp result hp
          | k => throwError "unexpected congruence argument {repr k}"
        return result
      if let some v ← delta? a (transportConversionAliases.contains ·) then
        let h₁ ← mkHEqRefl a
        let h₂ ← transportMetadataHEq fuel v.headBeta b
        return ← mkAppM ``HEq.trans #[h₁,h₂]
      if let some v ← delta? b (transportConversionAliases.contains ·) then
        let h₁ ← transportMetadataHEq fuel a v.headBeta
        let h₂ ← mkHEqRefl b
        return ← mkAppM ``HEq.trans #[h₁,h₂]
      match a,b with
      | .const n us, .const m vs =>
        if n == m && us.length == vs.length then
          if ← (us.zip vs).allM (fun (u,v) => isLevelDefEq u v) then
            return ← mkHEqRefl a
      | .sort u, .sort v =>
        if ← isLevelDefEq u v then return ← mkHEqRefl a
      | _, _ => pure ()
      if ← withTransparency .default (isDefEq a b) then
        return ← mkHEqRefl a
      throwError "structural conversion stopped at {a.getAppFn.constName?} \
        and {b.getAppFn.constName?}: {a} versus {b}"
    modify fun st => { st with proofs := st.proofs.insert (a,b) p }
    return p

@[local tactic coordinateStructuralExact] private meta def evalCoordinateStructuralExact : Tactic :=
    fun stx => withMainContext do
  let h : TSyntax `term := ⟨stx[1]⟩
  let p ← elabTerm h none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let p ← instantiateMVars p
  let source ← instantiateMVars (← inferType p)
  let target ← instantiateMVars (← getMainTarget)
  let (heq, _) ← (transportMetadataHEq 1000 source target).run {}
  let eq ← mkAppM ``eq_of_heq #[heq]
  let result ← mkAppM ``Eq.mp #[eq,p]
  (← getMainGoal).assign result
  replaceMainGoal []

private theorem square_paste {C : Type*} [Category C]
    {A B D E F G : C} (t : A ⟶ B) (qB : B ⟶ D) (qA : A ⟶ E)
    (r : E ⟶ D) (hD : D ⟶ G) (hE : E ⟶ F) (r' : F ⟶ G)
    (hq : t ≫ qB = qA ≫ r) (hn : hE ≫ r' = r ≫ hD) :
    t ≫ (qB ≫ hD) = (qA ≫ hE) ≫ r' := by
  rw [← Category.assoc, hq, Category.assoc, ← hn, ← Category.assoc]

private theorem tensor_refinement_paste
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D)
    {A B : C} (r : A ⟶ B) (L : C) {A' B' : D}
    (qB : S.obj B ⟶ B') (qA : S.obj A ⟶ A') (r' : A' ⟶ B')
    (μA : S.obj (A ⊗ L) ⟶ S.obj A ⊗ S.obj L)
    (μB : S.obj (B ⊗ L) ⟶ S.obj B ⊗ S.obj L)
    (hn : μA ≫ (S.map r ⊗ₘ 𝟙 (S.obj L)) = S.map (r ⊗ₘ 𝟙 L) ≫ μB)
    (hq : S.map r ≫ qB = qA ≫ r') :
    S.map (r ▷ L) ≫ (μB ≫ (qB ▷ S.obj L)) =
      (μA ≫ (qA ▷ S.obj L)) ≫ (r' ▷ S.obj L) := by
  simp only [tensorHom_id] at hn ⊢
  rw [← Category.assoc, ← hn, Category.assoc, ← comp_whiskerRight,
    hq, comp_whiskerRight]
  simp only [Category.assoc]

private theorem tensor_refinement_paste_map_id
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D)
    {A B : C} (r : A ⟶ B) (L : C) {A' B' : D}
    (qB : S.obj B ⟶ B') (qA : S.obj A ⟶ A') (r' : A' ⟶ B')
    (μA : S.obj (A ⊗ L) ⟶ S.obj A ⊗ S.obj L)
    (μB : S.obj (B ⊗ L) ⟶ S.obj B ⊗ S.obj L)
    (hn : μA ≫ (S.map r ⊗ₘ S.map (𝟙 L)) = S.map (r ⊗ₘ 𝟙 L) ≫ μB)
    (hq : S.map r ≫ qB = qA ≫ r') :
    S.map (r ▷ L) ≫ (μB ≫ (qB ▷ S.obj L)) =
      (μA ≫ (qA ▷ S.obj L)) ≫ (r' ▷ S.obj L) := by
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at hn ⊢
  rw [← Category.assoc, ← hn, Category.assoc, ← comp_whiskerRight,
    hq, comp_whiskerRight]
  simp only [Category.assoc]

private theorem geometric_refinement_exchange
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (v : Y' ⟶ Y) [IsIso v] {c d : Compactification f} (r : c.Refinement d)
    (K : CompactificationReindexing.D Λ X)
    (L : CompactificationReindexing.D Λ Y) :
    (CompactificationReindexing.P Λ v).map
        ((CompactificationReindexing.refinement Λ r).app
          (K ⊗ (CompactificationReindexing.P Λ f).obj L)) ≫
      (CompactificationReindexing.exchange Λ c v).app
          (K ⊗ (CompactificationReindexing.P Λ f).obj L) =
    (CompactificationReindexing.exchange Λ d v).app
        (K ⊗ (CompactificationReindexing.P Λ f).obj L) ≫
      (CompactificationReindexing.refinement Λ
        (CompactificationReindexing.refinementBaseChange r v)).app
          ((CompactificationReindexing.P Λ (pullback.fst f v)).obj
            (K ⊗ (CompactificationReindexing.P Λ f).obj L)) := by
  exact CompactificationReindexing.refinement_exchange Λ r v _

private theorem refinement_naturality
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    {A B : CompactificationReindexing.D Λ X} (h : A ⟶ B) :
    (CompactificationReindexing.F Λ d).map h ≫
        (CompactificationReindexing.refinement Λ r).app B =
      (CompactificationReindexing.refinement Λ r).app A ≫
        (CompactificationReindexing.F Λ c).map h := by
  exact (CompactificationReindexing.refinement Λ r).naturality h

private theorem geometric_tensor_input_naturality
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (v : Y' ⟶ Y) [IsIso v] {c d : Compactification f} (r : c.Refinement d)
    (K : CompactificationReindexing.D Λ X)
    (L : CompactificationReindexing.D Λ Y) :
    (CompactificationReindexing.F Λ (d.baseChange v)).map
        (CompactificationReindexing.tensorInput Λ v K L) ≫
      (CompactificationReindexing.refinement Λ
        (CompactificationReindexing.refinementBaseChange r v)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K ⊗
          (CompactificationReindexing.P Λ (pullback.snd f v)).obj
            ((CompactificationReindexing.P Λ v).obj L)) =
    (CompactificationReindexing.refinement Λ
        (CompactificationReindexing.refinementBaseChange r v)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj
          (K ⊗ (CompactificationReindexing.P Λ f).obj L)) ≫
      (CompactificationReindexing.F Λ (c.baseChange v)).map
        (CompactificationReindexing.tensorInput Λ v K L) := by
  exact refinement_naturality (CompactificationReindexing.refinementBaseChange r v)
    (CompactificationReindexing.tensorInput Λ v K L)

private def geometric_beta_native
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (v : Y' ⟶ Y) [IsIso v] {c d : Compactification f} (r : c.Refinement d)
    (K : CompactificationReindexing.D Λ X)
    (L : CompactificationReindexing.D Λ Y) :=
  (square_paste (C := CompactificationReindexing.D Λ Y')
    (A := (CompactificationReindexing.P Λ v).obj
      ((CompactificationReindexing.F Λ d).obj
        (K ⊗ (CompactificationReindexing.P Λ f).obj L)))
    (B := (CompactificationReindexing.P Λ v).obj
      ((CompactificationReindexing.F Λ c).obj
        (K ⊗ (CompactificationReindexing.P Λ f).obj L)))
    (D := (CompactificationReindexing.F Λ (c.baseChange v)).obj
      ((CompactificationReindexing.P Λ (pullback.fst f v)).obj
        (K ⊗ (CompactificationReindexing.P Λ f).obj L)))
    (E := (CompactificationReindexing.F Λ (d.baseChange v)).obj
      ((CompactificationReindexing.P Λ (pullback.fst f v)).obj
        (K ⊗ (CompactificationReindexing.P Λ f).obj L)))
    (F := (CompactificationReindexing.F Λ (d.baseChange v)).obj
      ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K ⊗
        (CompactificationReindexing.P Λ (pullback.snd f v)).obj
          ((CompactificationReindexing.P Λ v).obj L)))
    (G := (CompactificationReindexing.F Λ (c.baseChange v)).obj
      ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K ⊗
        (CompactificationReindexing.P Λ (pullback.snd f v)).obj
          ((CompactificationReindexing.P Λ v).obj L)))
    ((CompactificationReindexing.P Λ v).map
      ((CompactificationReindexing.refinement Λ r).app
        (K ⊗ (CompactificationReindexing.P Λ f).obj L)))
    ((CompactificationReindexing.exchange Λ c v).app
      (K ⊗ (CompactificationReindexing.P Λ f).obj L))
    ((CompactificationReindexing.exchange Λ d v).app
      (K ⊗ (CompactificationReindexing.P Λ f).obj L))
    ((CompactificationReindexing.refinement Λ
      (CompactificationReindexing.refinementBaseChange r v)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj
          (K ⊗ (CompactificationReindexing.P Λ f).obj L)))
    ((CompactificationReindexing.F Λ (c.baseChange v)).map
      (CompactificationReindexing.tensorInput Λ v K L))
    ((CompactificationReindexing.F Λ (d.baseChange v)).map
      (CompactificationReindexing.tensorInput Λ v K L))
    ((CompactificationReindexing.refinement Λ
      (CompactificationReindexing.refinementBaseChange r v)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K ⊗
          (CompactificationReindexing.P Λ (pullback.snd f v)).obj
            ((CompactificationReindexing.P Λ v).obj L)))
    (geometric_refinement_exchange v r K L)
    (geometric_tensor_input_naturality v r K L))

private theorem geometric_beta
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (v : Y' ⟶ Y) [IsIso v] {c d : Compactification f} (r : c.Refinement d)
    (K : CompactificationReindexing.D Λ X)
    (L : CompactificationReindexing.D Λ Y) :
    integralBetaRefinementCoordinate r v K L := by
  dsimp only [integralBetaRefinementCoordinate]
  coordinate_structural_exact (geometric_beta_native v r K L)

private def geometric_alpha_native
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (v : Y' ⟶ Y) [IsIso v] {c d : Compactification f} (r : c.Refinement d)
    (K : CompactificationReindexing.D Λ X)
    (L : CompactificationReindexing.D Λ Y) :=
  tensor_refinement_paste_map_id
    (C := CompactificationReindexing.D Λ Y)
    (D := CompactificationReindexing.D Λ Y') (CompactificationReindexing.P Λ v)
    ((CompactificationReindexing.refinement Λ r).app K) L
    ((CompactificationReindexing.exchange Λ c v).app K)
    ((CompactificationReindexing.exchange Λ d v).app K)
    ((CompactificationReindexing.refinement Λ
      (CompactificationReindexing.refinementBaseChange r v)).app
        ((CompactificationReindexing.P Λ (pullback.fst f v)).obj K))
    (((leftDerivedUpperStarTensor Λ v).app
      ((CompactificationReindexing.F Λ d).obj K)).app L)
    (((leftDerivedUpperStarTensor Λ v).app
      ((CompactificationReindexing.F Λ c).obj K)).app L)
    (by
      coordinate_structural_exact (leftDerivedUpperStarTensor_naturality Λ v
        ((CompactificationReindexing.refinement Λ r).app K) (𝟙 L)))
    (CompactificationReindexing.refinement_exchange Λ r v K)

private theorem geometric_alpha
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (v : Y' ⟶ Y) [IsIso v] {c d : Compactification f} (r : c.Refinement d)
    (K : CompactificationReindexing.D Λ X)
    (L : CompactificationReindexing.D Λ Y) :
    integralAlphaRefinementCoordinate r v K L := by
  dsimp only [integralAlphaRefinementCoordinate]
  simp only [tensorHom_id]
  coordinate_structural_exact (geometric_alpha_native v r K L)

private def scalar_tensor_naturality_raw {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) (K : CompactificationReindexing.D Λ.X X)
    (L : CompactificationReindexing.D Λ.X Y) :=
  CategoryTheory.Functor.OplaxMonoidal.δ_natural_left (scalarSixChange a Y)
    ((CompactificationReindexing.refinement Λ.X r).app K) L

private theorem scalar_tor_interval {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (X : Scheme.{u}) (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (lo hi : ℤ) (ht : _root_.DerivedCategory.torAmplitudeIn _ lo hi K) :
    _root_.DerivedCategory.torAmplitudeIn _ lo hi ((scalarSixChange a X).obj K) := by
  let F := Mod.extendScalars (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  obtain ⟨P, hge, hle, hflat, ⟨eP⟩⟩ :=
    (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat lo hi K).mp ht
  have hk := CochainComplex.kFlat_of_bounded_of_flat P lo hi hflat
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hk
  let P' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let e : _root_.DerivedCategory.Q.obj P' ≅ F.leftDerivedFunctor.obj K :=
    ((_root_.DerivedCategory.quotientCompQhIso _).app P').symm ≪≫
      (asIso (F.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj P))).symm ≪≫
      F.leftDerivedFunctor.mapIso ((_root_.DerivedCategory.quotientCompQhIso _).app P ≪≫ eP)
  apply (_root_.DerivedCategory.torAmplitudeIn _ lo hi).prop_of_iso e
  exact _root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat P' lo hi
    (fun n ↦ CategoryTheory.Functor.PreservesFlat.flat_obj (F := F) (hflat n))

end AlgebraicGeometry.ProEtale.CondensedRing
