# WeilConjectures.PrimitiveCounit.RoosRealization

## Reason

The concrete dependent record took 14–23 seconds in the kernel on its own. Together
with the other definitions the item was rejected at 82 seconds. Factor precisely
the same three fields through a generic record, so its recursor is checked without
the large concrete derived-category terms. The projection and resolution predicates
are unchanged. This changes the representation, not its mathematical content.

## Old

```lean
structure RoosRealization (W : Scheme.{t}) where
  comparison : RoosComparison l E W
  projection : RoosProjection l E W comparison
  resolution : RoosResolution l E W comparison
```

## New

```lean
structure NormalizedComparison (T : Type v) (P Q : T → Prop) where
  comparison : T
  projection : P comparison
  resolution : Q comparison

/-- One natural projection-compatible Roos realization, normalized on every resolution.
The actual inclusion roosι has zero shifted coordinate, as defined in StrictRoosModel.
Source: Stacks 0941 and lem-weil-strict-roos-comparison
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
abbrev RoosRealization (W : Scheme.{t}) : Type _ :=
  NormalizedComparison (RoosComparison l E W)
    (RoosProjection l E W) (RoosResolution l E W)

namespace RoosRealization
variable {l E}
abbrev mk {W : Scheme.{t}} (comparison : RoosComparison l E W)
    (projection : RoosProjection l E W comparison)
    (resolution : RoosResolution l E W comparison) : RoosRealization l E W :=
  ⟨comparison, projection, resolution⟩
abbrev comparison {W : Scheme.{t}} (ρ : RoosRealization l E W) :
    RoosComparison l E W := NormalizedComparison.comparison ρ
abbrev projection {W : Scheme.{t}} (ρ : RoosRealization l E W) :
    RoosProjection l E W ρ.comparison := NormalizedComparison.projection ρ
abbrev resolution {W : Scheme.{t}} (ρ : RoosRealization l E W) :
    RoosResolution l E W ρ.comparison := NormalizedComparison.resolution ρ
end RoosRealization
```

`inverseEvaluation` receives an explicit annotation of its previously inferred type;
its choice expression stays verbatim. `finiteTensorBridge` unfolds only
`unrestrictedIntegralReductionFunctor`, whose definition is already
`scalarReductionExtension`; its value remains the identity isomorphism. All existing
theorem statements and public imports are retained. The new generic record has no
postponed data or proofs. Constructor and projection names are retained as wrappers.
Generated eliminators are replaced by those of `NormalizedComparison`; no existing
source uses a named Roos eliminator. This definition occurs below targets and its
mathematical equivalence should be included in the independent statement review.

## Users

`tools/downstream.py Sheaf.Paper.CompletedPrimitiveCounitComparison --uses RoosRealization`
finds the following users. They use the type and field projections; no consumer
constructs the record through a named eliminator.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | R6 | definition and proof repair |
| Sheaf.Paper.CompletedUnitPullbackData | unclaimed | same type and field interface; no source changes |
| Sheaf.Paper.ExpressionCounitSubstitutionCoherence | unclaimed | same type and field interface; no source changes |
| Sheaf.Paper.FiniteExpressionReductionComparison | unclaimed | same type and field interface; no source changes |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | U4 | same type and field interface; no source changes |
| Sheaf.Paper.NormalizedTensorConstraintTransport | unclaimed | same type and field interface; no source changes |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | W4 | same type and field interface; no source changes |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | same type and field interface; no source changes |

## Status

landed 20261025T203003-L-2773316 2026-10-25 (merge of deliver/R6/Sheaf.Paper.CompletedPrimitiveCounitComparison)
