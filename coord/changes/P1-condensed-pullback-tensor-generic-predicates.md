# SupportDerivedTensorComparisonFamily and SupportDerivedTensorNormalization

## Reason

The existing concrete definitions elaborate the derived tensor and localization
instances repeatedly for sheaf module categories. Compiling a proof that instantiates
the generic tensor comparison then exceeds 60 seconds even when its naturality,
normalization and uniqueness obligations are replaced by diagnostic placeholders.
The abstract comparison proof itself compiles. This is the nested-instance-proof
comparison problem documented in the source library's
`CategoryTheory/DerivedCategory/Complete/Defs.lean`, implementation notes.

Factor the family and normalization predicates through generic definitions. Their
bodies still specify the same derived tensor, the same two-variable naturality,
the same exact-functor factorization maps and the same lax localization maps.
`derivedTensor` is `curriedTensor` by its source definition. The old
`SupportTensorDescentSquare` expands to precisely the equation in the new generic
predicate. The ordinary complex comparison is passed unchanged as a parameter.
No flatness or adjointness assumption is added to either support predicate or to
any public theorem. The generic existence/uniqueness proof is private.

The new generic definitions support this existing definition node; they contain
real types and predicates, no choices or postponed data. No source-library file
is edited. This is an implementation refactor with unchanged mathematical meaning;
the target-definition review must verify that equivalence. `Challenge.lean` is unchanged.

## Old

```lean
def SupportDerivedTensorComparisonFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ∀ K M : DerivedCategory (supportModules Λ Y),
    (supportPullback Λ f).mapDerivedCategory.obj (((derivedTensor Λ Y).obj K).obj M) ≅
      ((derivedTensor Λ X).obj ((supportPullback Λ f).mapDerivedCategory.obj K)).obj
        ((supportPullback Λ f).mapDerivedCategory.obj M)

/-- Naturality and the localization square on total-complex representatives.
Source: Stacks Tags 06YL and 0G7D
(blueprint: def-sfb-condensed-pullback-tensor-comparison).
The tensor maps are those of the existing derivedTensor functors and lax localization. -/
def SupportDerivedTensorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : SupportDerivedTensorComparisonFamily Λ f) : Prop :=
  (∀ (K K' M M' : DerivedCategory (supportModules Λ Y)) (a : K ⟶ K') (b : M ⟶ M'),
    (supportPullback Λ f).mapDerivedCategory.map
        (((derivedTensor Λ Y).map a).app M ≫ ((derivedTensor Λ Y).obj K').map b) ≫
        (e K' M').hom =
      (e K M).hom ≫
        ((derivedTensor Λ X).map ((supportPullback Λ f).mapDerivedCategory.map a)).app
          ((supportPullback Λ f).mapDerivedCategory.obj M) ≫
        ((derivedTensor Λ X).obj ((supportPullback Λ f).mapDerivedCategory.obj K')).map
          ((supportPullback Λ f).mapDerivedCategory.map b)) ∧
  ∀ A B : CochainComplex (supportModules Λ Y) ℤ,
    SupportTensorDescentSquare
      (DerivedCategory.Q (C := supportModules Λ Y))
      (DerivedCategory.Q (C := supportModules Λ X))
      ((supportPullback Λ f).mapHomologicalComplex (.up ℤ))
      (supportPullback Λ f).mapDerivedCategory
      (supportPullback Λ f).mapDerivedCategoryFactors
      (HomologicalComplex.tensorObj A B)
      (HomologicalComplex.tensorObj
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B))
      (((derivedTensor Λ Y).obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B))
      (((derivedTensor Λ X).obj
        ((supportPullback Λ f).mapDerivedCategory.obj (DerivedCategory.Q.obj A))).obj
          ((supportPullback Λ f).mapDerivedCategory.obj (DerivedCategory.Q.obj B)))
      (((derivedTensor Λ X).obj
        (DerivedCategory.Q.obj
          (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A))).obj
        (DerivedCategory.Q.obj
          (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B)))
      (@Functor.LaxMonoidal.μ _ _ _ _ _ _
        (DerivedCategory.Q (C := supportModules Λ Y)) (laxMonoidal_Q Λ Y) A B)
      (@Functor.LaxMonoidal.μ _ _ _ _ _ _
        (DerivedCategory.Q (C := supportModules Λ X)) (laxMonoidal_Q Λ X)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A)
        (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj B))
      (((derivedTensor Λ X).map
        ((supportPullback Λ f).mapDerivedCategoryFactors.hom.app A)).app
          ((supportPullback Λ f).mapDerivedCategory.obj (DerivedCategory.Q.obj B)) ≫
        ((derivedTensor Λ X).obj
          (DerivedCategory.Q.obj
            (((supportPullback Λ f).mapHomologicalComplex (.up ℤ)).obj A))).map
          ((supportPullback Λ f).mapDerivedCategoryFactors.hom.app B))
      (supportComplexTensorComparison Λ f A B)
      (e (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B))
```

## New

The following generic predicates are formed in the existing generic categorical
context (Grothendieck abelian closed braided monoidal categories with functorial
flat resolutions and an exact additive functor F). Lean omits unused assumptions.

```lean
def ExactDerivedTensorComparisonFamily :=
  ∀ K M : DerivedCategory C,
    F.mapDerivedCategory.obj (K ⊗ M) ≅
      F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj M

/-- Naturality and the total-complex square for a specified ordinary comparison.
Source: Stacks Tags 06YL and 0G7D
(blueprint: def-sfb-condensed-pullback-tensor-comparison).
This is the generic form of `SupportDerivedTensorNormalization`: tensor morphisms
are written as the two maps of the curried tensor functor. -/
def ExactDerivedTensorNormalization
    (d : ∀ A B : CochainComplex C ℤ,
      (F.mapHomologicalComplex (.up ℤ)).obj (A ⊗ B) ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj A ⊗
          (F.mapHomologicalComplex (.up ℤ)).obj B)
    (e : ExactDerivedTensorComparisonFamily F) : Prop :=
  (∀ (K K' M M' : DerivedCategory C) (a : K ⟶ K') (b : M ⟶ M'),
    F.mapDerivedCategory.map
        (((curriedTensor _).map a).app M ≫ ((curriedTensor _).obj K').map b) ≫
        (e K' M').hom =
      (e K M).hom ≫
        ((curriedTensor _).map (F.mapDerivedCategory.map a)).app
          (F.mapDerivedCategory.obj M) ≫
        ((curriedTensor _).obj (F.mapDerivedCategory.obj K')).map
          (F.mapDerivedCategory.map b)) ∧
  ∀ A B : CochainComplex C ℤ,
    F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q A B) ≫
      F.mapDerivedCategoryFactors.hom.app (A ⊗ B) ≫ DerivedCategory.Q.map (d A B) =
    (e (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom ≫
      (((curriedTensor _).map (F.mapDerivedCategoryFactors.hom.app A)).app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj B)) ≫
        ((curriedTensor _).obj
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj A))).map
            (F.mapDerivedCategoryFactors.hom.app B)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj A)
        ((F.mapHomologicalComplex (.up ℤ)).obj B)
```

The existing support predicates specialize these constructions:

```lean
def SupportDerivedTensorComparisonFamily {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ExactDerivedTensorComparisonFamily (supportPullback Λ f)

/-- Naturality and the localization square on total-complex representatives.
Source: Stacks Tags 06YL and 0G7D
(blueprint: def-sfb-condensed-pullback-tensor-comparison).
The tensor maps are those of the existing derivedTensor functors and lax localization. -/
def SupportDerivedTensorNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : SupportDerivedTensorComparisonFamily Λ f) : Prop :=
  ExactDerivedTensorNormalization (supportPullback Λ f)
    (supportComplexTensorComparison Λ f) e
```

## Users

The source scan reports 168 transitive importers, listed below with their
current claim records. Textual uses of the two changed predicate names occur only
in the item. Four other modules use `supportDerivedTensorComparison`:
`CondensedOpenClosedInternalHomMaps`, `CondensedOpenClosedInternalHom`,
`CondensedSupportProjectionFormula`, and `SixFunctors.ClosedImmersionTensorProjection`.
The family remains a family of isomorphisms between the same derived tensor objects,
and the normalization conjuncts retain their existing order and equations. No user
statement changes or forced adaptations are intended.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison | P1 | Refactor predicates; prove the existing uniqueness theorem. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | F4 | Same mathematical tensor and square; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Same mathematical tensor and square; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same mathematical tensor and square; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same mathematical tensor and square; no adaptation. |
| TargetsCheck | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same mathematical tensor and square; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same mathematical tensor and square; no adaptation. |


Validation: the complete item compiles without warnings (57.1 s; a profiled
single-file check also passed at 35.8 s). A separate importer test using the
compiled item verifies both the original derived-tensor family type and the exact
published naturality equation (19.3 s). Another importer copies the entire old
normalization body verbatim and proves its equivalence with the new predicate by
`rfl` (24.2 s). Thus the complete old specification is definitionally unchanged.

Three unchanged consumers were tested against the item artifact:
`CondensedOpenClosedInternalHomMaps` (held by F4),
`CondensedSupportProjectionFormula` (unclaimed), and
`SixFunctors.ClosedImmersionTensorProjection` (unclaimed).
They fail with the same error headers and counts against the unchanged published
item: respectively 13, 2, and 1. The first lacks
`PreservesFiniteColimits (lowerStar Λ i)`; the latter two report kernel/generalize
errors from the changed `closedSupport_lowerStarExact` interface in the existing
closed-support dependencies. These are baseline failures, not forced adaptations
of this delivery; their sources are not included or edited. This report supplies
the discrepancy upward for the maintainer and the current consumer owner.

## Status

landed 20261021T061554-L-1793200 2026-10-21 (merge of deliver/P1/Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison)
