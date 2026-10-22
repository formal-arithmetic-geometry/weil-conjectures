# WeilConjectures.integralTowerInverseImageUnit_existsUnique

## Reason

Stage-3 preflight requires a change record for the added proof elaboration context
(`open`, universes and section variables) in
`Sheaf.Paper.IntegralTowerInverseImageUnit`. Its conservative syntax check also
identified three private instances. They are now private theorems registered
with explicitly local instance attributes, so importing modules receive no new
instance registrations.

The item is held by G4. Only this module is changed. The theorem is proved from the
existing coefficient/site interfaces and Mathlib. Every existing public signature,
definition body, declaration docstring and public import stays identical. No target
statement, definition meaning or unit route changes. No adopted source-library file
is changed.

## Old

Original declaration signature, verbatim:

```lean
theorem integralTowerInverseImageUnit_existsUnique :
    ∃! a : coefficientSequenceRestriction l E Y ⋙ integralTowerInverseImage l E g ≅
        integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : X.ProEt)
        (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
        ((a.hom.app M).app (op n)).val.app (op U)
            (integralComparisonRestrictedSection l E Y M n
              (op ((proEtaleIsoPostcompose g).obj U)) x) =
          integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E g).obj M) n (op U)
            (((integralComparisonSequencePullback l E g).obj M).val.map
              (CategoryTheory.Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
              (integralComparisonSequenceGenerator l E g M n
                ((proEtaleIsoPostcompose g).obj U) x))
```

The module declares `universe t u` and opens
`CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry`. Its existing
scheme opens, section parameters, compiler options and negative instance attributes
are as in the shared source. There are no private tower-comparison helpers.

## New

The declaration signature is unchanged, verbatim:

```lean
theorem integralTowerInverseImageUnit_existsUnique :
    ∃! a : coefficientSequenceRestriction l E Y ⋙ integralTowerInverseImage l E g ≅
        integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : X.ProEt)
        (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
        ((a.hom.app M).app (op n)).val.app (op U)
            (integralComparisonRestrictedSection l E Y M n
              (op ((proEtaleIsoPostcompose g).obj U)) x) =
          integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E g).obj M) n (op U)
            (((integralComparisonSequencePullback l E g).obj M).val.map
              (CategoryTheory.Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
              (integralComparisonSequenceGenerator l E g M n
                ((proEtaleIsoPostcompose g).obj U) x))
```

Its proof constructs the level comparison from the actual sequence adjunction
unit and comma restriction, proves transition compatibility, assembles the whole
natural isomorphism, and proves uniqueness on all sections.

The module now declares `universe t u v w`, adding universe names for private
generic-category helpers, and additionally opens `CategoryTheory.Functor`.
Generic private helpers have their own explicitly declared category parameters;
`section GenericComma` scopes the shared generic parameters. The option
`backward.defeqAttrib.useBackward` is enabled during the private proof development
(and locally for the restricted-section transition lemma) to use the existing
cast/interface equations without expensive unfolding. All new helper declarations
are private and proved or constructed without holes. Private proof imports are
`Mathlib.CategoryTheory.Sites.CoverLifting` and
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`.

The continuity helpers are private theorems, with only these local registrations:

```lean
attribute [local instance] towerPostcomposeBaseChangeContinuous
attribute [local instance] towerPostcomposeSliceContinuous
attribute [local instance] towerPostcomposeSliceBaseChangeContinuous
```

Their types assert continuity of the composites of the postcomposition functor
with base change, a level inclusion, and a level inclusion followed by sequence
base change. Their proofs are applications of `Functor.isContinuous_comp` to
existing continuous functors. No global instance, simp rule or notation is added.
The original global instance declarations and negative instance attributes remain
verbatim. The extra `omit [IsIso g] in` on the private generator-transition lemma
removes an unused section assumption reported by the compiler linter.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntegralTowerInverseImageUnit --uses
WeilConjectures.integralTowerInverseImageUnit_existsUnique` reports 116 transitive
consumers. Its textual declaration search finds only the item itself and
`Sheaf.Paper.IntegralInverseImageComparisonComposition`. All transitive consumers
are listed below with the current claim holders. There is no interface or semantic
change, and no consumer is edited or requires adaptation. The helper instance
registrations are local to the item module.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | G4 | Assigned theorem proved; elaboration context and local proof instances documented. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionMixedDescent` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ConstantGeometricStalkUnit` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FourierArtinSchreierProperties` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ImmersionWeilPullbackLocalBehavior` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralCompositionCounitImages` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LocalFrobeniusCoefficientExtension` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.OrientationCoefficientTwists` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.OrientationFiniteCoefficientTwists` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.OrientationFiniteReductionTwists` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.PointSystemPowerRoosCoherence` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.PointSystemRoosTransport` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.PointSystemTransportDescent` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.PointTransportStrictQuotient` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.PointWeilHeartFlag` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.RealWeights` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.SixFunctorOrientation` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.SixFunctorOrientationDatum` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.SixFunctorOrientationFamily` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.SixFunctorOrientationFiniteFamily` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.SixFunctorOrientationHigherPair` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.SixFunctorOrientationStageCompatibility` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WeilTateTwistFrobenius` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Existing signatures and definitions unchanged; no adaptation required. |

## Status

landed 20261022T011841-L-3224229 2026-10-22 (merge of deliver/G4/Sheaf.Paper.IntegralTowerInverseImageUnit)
