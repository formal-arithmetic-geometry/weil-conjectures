# pullbackTensorUniqueChoice and normalized comparison selections

## Reason

Delivery path: `coord/changes/completed-pullback-tensor-unique-choice.md`.
This record is included directly in the repaired J6 packet; it needs no
reviewer-side basename fix. If an override is needed, `tools/batch_land.py`
expects `completed-pullback-tensor-unique-choice.change.md`, not the repository
basename. Returned head: `0a67bf11053`.

The original module and its one-hole proof update repeatedly exceeded the 60-second
file limit. Prefix profiling located repeated kernel checking of large normalization
predicates in the selected comparison definitions. Factoring the existing unique-choice
operation into a named definition reduces repetition: the one-hole full module compiled
in 41.1 seconds (a second version in 46.0 seconds). This is a definitional abbreviation
of exactly the existing choice, not a replacement witness. No signature or normalization
statement changes, and no target meaning changes.

The delivered ordinary-limit proof uses local transparency controls for the standard
derived category and derived-functor records. These affect proof elaboration only;
no imported attribute is exported or changed. The direct and inverse evaluation proof
attempts remain only in the scratchpad.

## Old

```lean
def pullbackTensorSequenceRing {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorSequenceRing_existsUnique l E f).exists.choose
```

```lean
def pullbackTensorReductionModel (W : Scheme.{u}) :=
  (pullbackTensorReductionModel_existsUnique l E W).exists.choose
```

```lean
def pullbackTensorReductionEvaluation (W : Scheme.{u}) (n : ℕ) :=
  (pullbackTensorReductionEvaluation_existsUnique l E W n).exists.choose
```

```lean
def pullbackTensorSequenceDirectEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose
```

```lean
def pullbackTensorSequenceInverseEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose
```

```lean
def pullbackTensorRoosModel (W : Scheme.{u}) :=
  (pullbackTensorRoosModel_existsUnique l E W).exists.choose
```

```lean
def pullbackTensorPullbackTower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (pullbackTensorPullbackTower_existsUnique l E f P).exists.choose
```

```lean
def pullbackTensorTensorTower (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  (pullbackTensorTensorTower_existsUnique l E W P Q).exists.choose
```

```lean
def pullbackTensorIntegralPullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorIntegralPullbackModel_existsUnique l E f).exists.choose
```

```lean
def pullbackTensorIntegralTensorModel (W : Scheme.{u}) :=
  (pullbackTensorIntegralTensorModel_existsUnique l E W).exists.choose
```

```lean
def pullbackTensorSequenceCochain {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose
```

```lean
def pullbackTensorSystemComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorSystemComparison_existsUnique l E f).exists.choose
```

```lean
def pullbackTensorLevelIntrinsic {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorLevelIntrinsic_existsUnique l E f n).exists.choose
```

```lean
def pullbackTensorDerivedEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose
```

```lean
def pullbackTensorQuotientOrdinary {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :=
  (pullbackTensorQuotientOrdinary_existsUnique l E f h).exists.choose
```

```lean
def pullbackTensorQuotient {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  (pullbackTensorQuotient_existsUnique l E f h).exists.choose
```

```lean
def canonicalRationalPullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@RationalPullbackTensorComparison l _ E _ _ _ X Y f hX hY) := fun M N ↦
  ((@canonicalRationalPullbackTensor_existsUnique l _ E _ _ _ X Y f hX hY) M N).exists.choose
```

```lean
def canonicalCommonStagePullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@CommonStagePullbackTensorComparison l _ Ω _ _ _ X Y f hX hY) := fun P Q ↦
  ((@canonicalCommonStagePullbackTensor_existsUnique l _ Ω _ _ _ X Y f hX hY) P Q).exists.choose
```

## New

```lean
def pullbackTensorUniqueChoice {A : Sort*} {P : A → Prop} (h : ∃! x, P x) : A :=
  h.exists.choose

-- at the end of the module, after every use in it
attribute [reducible] pullbackTensorUniqueChoice
```

The wrapper is exported reducible (reviewer fix, 2026-10-25, re-applied on head
b557af6823fa). As a plain semireducible `def` it breaks
`Sheaf.Paper.DerivedPullbackTensorIso` (P4): there
`canonicalRationalPullbackTensor_associative_spec` unfolds
`canonicalRationalPullbackTensor` by `simpa only` and closes the goal against
`(… existsUnique …).exists.choose_spec` terms under
`backward.isDefEq.respectTransparency true`, which does not unfold a
semireducible wrapper inside implicit arguments ("Type mismatch: After
simplification"). The attribute is set only after the last use in this module,
so the elaboration of the module itself is unchanged.

```lean
def pullbackTensorSequenceRing {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorUniqueChoice (pullbackTensorSequenceRing_existsUnique l E f)
```

```lean
def pullbackTensorReductionModel (W : Scheme.{u}) :=
  pullbackTensorUniqueChoice (pullbackTensorReductionModel_existsUnique l E W)
```

```lean
def pullbackTensorReductionEvaluation (W : Scheme.{u}) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorReductionEvaluation_existsUnique l E W n)
```

```lean
def pullbackTensorSequenceDirectEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n)
```

```lean
def pullbackTensorSequenceInverseEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n)
```

```lean
def pullbackTensorRoosModel (W : Scheme.{u}) :=
  pullbackTensorUniqueChoice (pullbackTensorRoosModel_existsUnique l E W)
```

```lean
def pullbackTensorPullbackTower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  pullbackTensorUniqueChoice (pullbackTensorPullbackTower_existsUnique l E f P)
```

```lean
def pullbackTensorTensorTower (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  pullbackTensorUniqueChoice (pullbackTensorTensorTower_existsUnique l E W P Q)
```

```lean
def pullbackTensorIntegralPullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorUniqueChoice (pullbackTensorIntegralPullbackModel_existsUnique l E f)
```

```lean
def pullbackTensorIntegralTensorModel (W : Scheme.{u}) :=
  pullbackTensorUniqueChoice (pullbackTensorIntegralTensorModel_existsUnique l E W)
```

```lean
def pullbackTensorSequenceCochain {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorUniqueChoice (pullbackTensorSequenceCochain_existsUnique l E f)
```

```lean
def pullbackTensorSystemComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  pullbackTensorUniqueChoice (pullbackTensorSystemComparison_existsUnique l E f)
```

```lean
def pullbackTensorLevelIntrinsic {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorLevelIntrinsic_existsUnique l E f n)
```

```lean
def pullbackTensorDerivedEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorDerivedEvaluation_existsUnique l E f n)
```

```lean
def pullbackTensorQuotientOrdinary {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :=
  pullbackTensorUniqueChoice (pullbackTensorQuotientOrdinary_existsUnique l E f h)
```

```lean
def pullbackTensorQuotient {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  pullbackTensorUniqueChoice (pullbackTensorQuotient_existsUnique l E f h)
```

```lean
def canonicalRationalPullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@RationalPullbackTensorComparison l _ E _ _ _ X Y f hX hY) := fun M N ↦
  pullbackTensorUniqueChoice ((@canonicalRationalPullbackTensor_existsUnique
    l _ E _ _ _ X Y f hX hY) M N)
```

```lean
def canonicalCommonStagePullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@CommonStagePullbackTensorComparison l _ Ω _ _ _ X Y f hX hY) := fun P Q ↦
  pullbackTensorUniqueChoice ((@canonicalCommonStagePullbackTensor_existsUnique
    l _ Ω _ _ _ X Y f hX hY) P Q)
```

## Users

`tools/downstream.py Sheaf.Paper.CompletedPullbackTensorComparison --uses` was run
with every affected definition. The table lists its textual declaration consumers.
The current scan finds 55 textual consumers, including this module. Four additional
rows from the earlier scan are retained for archived or superseded consumers.
All uses keep their original types and values by unfolding `pullbackTensorUniqueChoice`.
Only the item module is edited; no forced adaptation is needed. All 16 direct importers
compile against the module with the reducible wrapper (reviewer check, 2026-10-25).

| module | group holding it | effect |
|---|---|---|
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor` unchanged. |
| `Sheaf.Paper.AdicProperAdjunctionRealization` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor` unchanged. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Definitional abbreviation only; `pullbackTensorDerivedEvaluation`, `pullbackTensorIntegralPullbackModel` unchanged. |
| `Sheaf.Paper.AdicQbarConstructibleRealization` | A8 | Definitional abbreviation only; `canonicalCommonStagePullbackTensor` unchanged. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | F7 | Definitional abbreviation only; `canonicalRationalPullbackTensor`, `pullbackTensorQuotient` unchanged. |
| `Sheaf.Paper.CanonicalTateArrowNaturality` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor`, `pullbackTensorQuotient` unchanged. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor` unchanged. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor` unchanged. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor` unchanged. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Definitional abbreviation only; `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.CompletedComparisonQuotientRealization` | unclaimed | Definitional abbreviation only; `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel`, `pullbackTensorReductionModel`, `pullbackTensorSequenceCochain` unchanged. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | J6 | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor`, `pullbackTensorDerivedEvaluation`, `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel`, `pullbackTensorLevelIntrinsic`, `pullbackTensorPullbackTower`, `pullbackTensorQuotient`, `pullbackTensorQuotientOrdinary`, `pullbackTensorReductionEvaluation`, `pullbackTensorReductionModel`, `pullbackTensorRoosModel`, `pullbackTensorSequenceCochain`, `pullbackTensorSequenceDirectEvaluation`, `pullbackTensorSequenceInverseEvaluation`, `pullbackTensorSequenceRing`, `pullbackTensorSystemComparison`, `pullbackTensorTensorTower` unchanged. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Definitional abbreviation only; `pullbackTensorIntegralTensorModel` unchanged. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor` unchanged. |
| `Sheaf.Paper.ConstructibleMateCoherence` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor`, `pullbackTensorDerivedEvaluation`, `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel`, `pullbackTensorLevelIntrinsic`, `pullbackTensorSequenceInverseEvaluation`, `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | P4 | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor`, `pullbackTensorDerivedEvaluation`, `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel`, `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | unclaimed | Definitional abbreviation only; `pullbackTensorDerivedEvaluation`, `pullbackTensorIntegralPullbackModel`, `pullbackTensorQuotient` unchanged. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Definitional abbreviation only; `pullbackTensorQuotient` unchanged. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | M3 | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence` | H5 | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor`, `pullbackTensorDerivedEvaluation`, `pullbackTensorIntegralTensorModel`, `pullbackTensorQuotient` unchanged. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Definitional abbreviation only; `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.MiddleExchangeProjectionBaseChange` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.PodCompletionReindexSubstitution` | unclaimed | Definitional abbreviation only; `pullbackTensorIntegralTensorModel` unchanged. |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | unclaimed | Definitional abbreviation only; `pullbackTensorIntegralTensorModel` unchanged. |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed | Definitional abbreviation only; `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.ReindexingSystemHomReductionSquare` | unclaimed | Definitional abbreviation only; `pullbackTensorDerivedEvaluation`, `pullbackTensorQuotient`, `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.SemilinearFieldOperationLifts` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Definitional abbreviation only; `canonicalRationalPullbackTensor`, `pullbackTensorQuotient` unchanged. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Definitional abbreviation only; `pullbackTensorDerivedEvaluation` unchanged. |
| `Sheaf.Paper.SystemTensorPresentationIdentification` | unclaimed | Definitional abbreviation only; `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Definitional abbreviation only; `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Definitional abbreviation only; `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed | Definitional abbreviation only; `pullbackTensorPullbackTower`, `pullbackTensorTensorTower` unchanged. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | V3 | Definitional abbreviation only; `canonicalCommonStagePullbackTensor`, `canonicalRationalPullbackTensor` unchanged. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeRealization` | unclaimed | Definitional abbreviation only; `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Definitional abbreviation only; `pullbackTensorDerivedEvaluation` unchanged. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Definitional abbreviation only; `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel` unchanged. |
| `Sheaf.SixFunctors.IntegralBasicRealization` | unclaimed | Definitional abbreviation only; `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel` unchanged. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Definitional abbreviation only; `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel`, `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.SixFunctors.IntegralExpressionRecursion` | unclaimed | Definitional abbreviation only; `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel` unchanged. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Definitional abbreviation only; `pullbackTensorReductionModel`, `pullbackTensorSequenceDirectEvaluation` unchanged. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Definitional abbreviation only; `pullbackTensorDerivedEvaluation`, `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed | Definitional abbreviation only; `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Definitional abbreviation only; `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Definitional abbreviation only; `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed | Definitional abbreviation only; `pullbackTensorSystemComparison` unchanged. |
| `Sheaf.Paper.AdicRealizationFamilyData` | unclaimed | Definitional abbreviation only; `canonicalCommonStagePullbackTensor` unchanged. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Definitional abbreviation only; `canonicalRationalPullbackTensor` unchanged. |

## Status

landed 20261025T163731-L-806478 2026-10-25 (merge of deliver/J6/Sheaf.Paper.CompletedPullbackTensorComparison)
