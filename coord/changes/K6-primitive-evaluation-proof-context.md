# PrimitiveCounit evaluation proof context

## Reason

The two completed evaluation proofs use fully proved private categorical helpers and
local reducibility settings to keep the chosen adjoints and module pushforwards folded.
These commands affect elaboration in this module only. They do not change any existing
public signature, public import, or exported attribute.

The identity comparison `finiteTensorBridge` now identifies the two scalar-extension
functors before rewriting their tensor-complex applications. Both functors use the same
universal witness, so this preserves the identity map and the definition's meaning.
No private helper occurs in the public definition. No consumer adaptation is needed.
Targets using this definition are reopened for the required definition-meaning review;
the reviewer should confirm that the bridge is still the same identity comparison.

## Old

The original context immediately before the evaluation-existence theorem was:

```lean
attribute [local irreducible] Functor.leftAdjoint
```

There was no evaluation-proof section or downstream local attribute for inverseEvaluation.

The previous tensor-bridge definition, verbatim:

```lean
def finiteTensorBridge (W : Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n) :=
  by
    change ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
            (.up ℤ)).obj P,
            ((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
              (.up ℤ)).obj Q))
    unfold unrestrictedIntegralReductionFunctor
    exact Iso.refl _
```

## New

The original universe context and all existing public declaration headers are unchanged.
The three new private helpers prove mate existence and unit-normalized uniqueness in
abstract categories. The evaluation proof section begins with:

```lean
section EvaluationProofs
attribute [local irreducible] Scheme.coefficientProEtaleModuleAdjunction
  Scheme.coefficientProEtaleModulePullback SheafOfModules.pushforward ringMap
```

The section closes before the existing assembly theorem. After the existing chosen
comparison definition, local attributes keep the comparison and system functors folded:

```lean
attribute [local irreducible] inverseEvaluation inverse direct
```

All private helpers are proved. The revised tensor bridge transports the functor equality
through complexes, the tensor functor, and restriction. Functors preserve identity maps,
so the resulting map remains the same identity comparison:

```lean
def finiteTensorBridge (W : Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n) :=
  by
    change ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
            (.up ℤ)).obj P,
            ((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
              (.up ℤ)).obj Q))
    have h : unrestrictedIntegralReductionFunctor l E W n =
        scalarReductionExtension l E W n := by
      unfold unrestrictedIntegralReductionFunctor scalarReductionExtension
        unrestrictedIntegralReductionExistence scalarReductionExistence
      rfl
    let e := NatIso.mapHomologicalComplex (eqToIso h) (.up ℤ)
    exact ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).mapIso
          ((e.app P).symm.prod (e.app Q).symm))
```

All other existing non-theorem bodies remain verbatim.

## Users

The following table is the full source import closure returned by
`tools/downstream.py Sheaf.Paper.CompletedPrimitiveCounitComparison --names`, plus
this item. Every existing public signature is unchanged and the tensor bridge retains its meaning,
so these consumers need no source edits. A textual use check for `finiteTensorBridge`
finds uses only in this module. No exported unfolding attribute is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | K6 | Two proofs filled; local context and tensor-bridge construction changed; signatures unchanged. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedUnitAdmissible | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedUnitMultiplicationComponents | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedUnitPullbackData | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedUnitPullbackTower | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedUnitReduction | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedUnitScalarNaturality | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.CompletedUnitStrictComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.ExpressionCounitSubstitutionCoherence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.FiniteExpressionReductionComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.NormalizedTensorConstraintTransport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryPullbackCompositionEvaluation | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | W4 | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Public signatures, definitions and imports unchanged; no adaptation. |

## Status

landed 20261026T023440-L-566781 2026-10-26 (merge of deliver/K6/Sheaf.Paper.CompletedPrimitiveCounitComparison)
