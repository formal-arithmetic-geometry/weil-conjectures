# AlgebraicGeometry.ProEtale.AffineOrderedIntegration.OrdinaryTensorActionEquation

## Reason

The fixed-scalar equation causes repeated kernel normalization of the concrete
module-sheaf tensor and pullback structures when applying the existing generic
compactification action law. Profiling separates fast elaboration from a kernel
timeout. State the literal equation once at a variable coefficient category,
and specialize that definition to ModuleCat A. The existing public signature
is unchanged; this is a change of expression sharing, not a new hypothesis or a
weakened equation. Both category-level laws have complete private proofs from
FiniteProjectionActionLaws.

## Old

```lean
def OrdinaryTensorActionEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (N₁ N₂ : Etale.DerivedCategoryModule A Y) : Prop :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  (Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) Y
    ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)
      N₁ N₂).hom ≫
    ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj N₁).obj N₂) ≫
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f N₁ N₂).hom ≫
      (Etale.derivedTensorAssociator (ModuleCat.{u + 1} A) X M
        ((Etale.ordinaryFinitePullback A f).obj N₁)
        ((Etale.ordinaryFinitePullback A f).obj N₂)).inv) =
  ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).map
    (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app N₁)).app N₂ ≫
    ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
        ((Etale.ordinaryFinitePullback A f).obj N₁))).app N₂
```

## New

The added public definition retains every projection map, associator, and
inverse-image tensor comparison in the old equation:

```lean
def OrdinaryTensorActionEquationForCategory
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
    (Etale.derivedTensorAssociator A Y
      ((Etale.rightDerivedLowerShriekOfCompactification A c).obj M) N₁
      N₂).hom ≫
      (((Etale.projectionMapOfCompactification A c).app M).app
        (((Etale.derivedTensor A Y).obj N₁).obj N₂)) ≫
      (Etale.rightDerivedLowerShriekOfCompactification A c).map
        (((Etale.derivedTensor A X).obj M).map
            (Etale.leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (Etale.derivedTensorAssociator A X M
            ((Etale.upperStar A f).leftDerivedFunctor.obj N₁)
            ((Etale.upperStar A f).leftDerivedFunctor.obj N₂)).inv) =
    ((Etale.derivedTensor A Y).map (((Etale.projectionMapOfCompactification
      A c).app M).app N₁)).app N₂ ≫
      (((Etale.projectionMapOfCompactification A c).app (((Etale.derivedTensor
        A X).obj M).obj ((Etale.upperStar A f).leftDerivedFunctor.obj N₁))).app N₂)
```

The existing definition becomes its specialization, with its original signature:

```lean
def OrdinaryTensorActionEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (N₁ N₂ : Etale.DerivedCategoryModule A Y) : Prop :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  OrdinaryTensorActionEquationForCategory (ModuleCat.{u + 1} A) f c M N₁ N₂
```

AffineSpacePurity.tensor unfolds to the displayed derivedTensor, and
AffineSpacePurity.inverseImage unfolds to upperStar.leftDerivedFunctor.
On the ordinary site ordinaryFinitePullback unfolds to that site's corresponding
upperStar.leftDerivedFunctor. These are exactly the canonical maps in the old
body. No choice of an isomorphism or of a replacement arrow is added. This covers
zero complexes, identity projections and empty schemes as well.

The body change is submitted for the standard definition-meaning review of
any affected target; its mathematical predicate and all target signatures are
unchanged. No actual trace, integration or exceptional-functor construction is
changed by this edit.

## Users

`tools/downstream.py Sheaf.Paper.AffineOrderedIntegrationTransposes --uses AlgebraicGeometry.ProEtale.AffineOrderedIntegration.OrdinaryTensorActionEquation` reports 101
transitive importers and only the item itself as a textual user. No external
consumer requires adaptation. The full importer census follows.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineOrderedIntegrationTransposes | C1 | CoordinateCoherence uses the identical canonical equation; coordinate_coherence applies its proved generic law. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDncNaturality | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDncSquare | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | A3 | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.ProjectionPurityAgreement | X3 | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | H3 | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No reference to OrdinaryTensorActionEquation; the canonical constructions and equation are unchanged. |

## Status

landed 20261026T001039-L-4164802 2026-10-26 (merge of deliver/C1/Sheaf.Paper.AffineOrderedIntegrationTransposes)
