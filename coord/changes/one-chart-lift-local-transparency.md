# AlgebraicGeometry.finitePresentation_one_chart_map_lift_at_stage

## Reason

The preflight treats the newly added local attribute command as a potential interface
change. This record documents that it is local elaboration control only. Unfolding
`tensorPullbackCompositionIso` and `openCoverTensorPullbackComparison` during the final
comparison expanded large adjunction terms and exhausted the compile budget. Making
these comparisons locally irreducible and explicitly reducing the let bindings and
`moduleBaseChange` makes the unchanged equation check directly. No existing definition,
statement, visibility, global attribute, or public import changes. The new ordinary
recovery definition likewise constructs the same equation with no postponed data.

## Old

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

The original declaration's full signature is unchanged; it is recorded verbatim in
`dag/nodes/sec-picard-framework/lem-pc-fp-one-chart-map-lift-at-stage.json`.

## New

```lean
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.openCoverTensorPullbackComparison

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

The local attributes apply only in this file, and the declaration-local options do not
change its exported statement. The linter option permits its unchanged unused `B` binder.

## Users

The declaration-level `tools/downstream.py --uses` search found the following users.
No user needs adaptation: both local attributes and options cease at the module boundary;
the exported declaration and its public imports stay identical. The 1342 modules in the
transitive import closure likewise see the same interface. No target changes meaning and
no target-statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLiftAtStage | F4 | Proof now compiles; signature identical. |
| Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLift | unclaimed in this clone | No exported interface change; no adaptation. |

## Status

landed 20261013T201748-L-3969017 2026-10-13 (merge of deliver/F4/Sheaf.AlgebraicGeometry.FinitePresentationOneChartMapLiftAtStage)
