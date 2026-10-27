# Restore the recorded coefficient comparison interfaces

## Reason

The current DAG still attaches two dependencies of the assigned constructibility
test to absent Lean modules. They belonged to the D8 delivery taken out after a
global consumer failure. This packet restores those existing interfaces rather
than withdrawing their nodes or changing the unit route. There is no current
local claim or rework row for either module.

## Old

`Sheaf.AlgebraicGeometry.CoefficientComparisonFixedPullback` and
`Sheaf.AlgebraicGeometry.CoefficientComparisonFiniteReflection` have no source
file in the current tree. Their existing nodes nevertheless specify
`AlgebraicGeometry.ProEtale.coefficientComparison_fixedPullback` and
`AlgebraicGeometry.ProEtale.coefficientComparison_finite_reflect`, with the
signatures preserved in the node copies included in this delivery.

## New

Restore both modules with exactly their recorded statements. The compatibility
isomorphism has a complete proof using constant-scalar equivalences, equality of
constant scalars under the comparison ring map, and uniqueness of left adjoints.
The finite reflection theorem retains its one named proof hole, source and full
proof in words. There are no new mathematical nodes. Only Lean restoration
provenance is updated in the two node copies. All helpers are private and proved;
no exported instance or attribute changes, definition repairs or source-library
changes are made.

## Users

| Module | Effect |
| --- | --- |
| `Sheaf.AlgebraicGeometry.CoefficientComparisonConstructibilityTest` | Imports and uses the restored compatibility theorem in both directions and reflection in the converse; its sole hole is closed. |
| `Sheaf.Paper.FiniteComparisonPresentation` | Unchanged consumer named in the old return. It type-checks against the packet without the earlier universe or missing-argument errors; its diagnostic compile exceeds the time limit (85.5 seconds). No edits or adaptations are delivered. |

No current source file imports either previously absent module. The assigned
module is their only direct importer in the delivered packet. No consumer
signature is changed and no forced adaptation is claimed.

## Status

landed 20261026T002008-L-48249 2026-10-26 (merge of deliver/M4/Sheaf.AlgebraicGeometry.CoefficientComparisonConstructibilityTest)
