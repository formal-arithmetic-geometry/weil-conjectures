## What changed

Replaced the proof hole in
`AlgebraicGeometry.Etale.vectorIntegration_restricted_chart_transport` by an assembly of
ordinary compact-support exchange naturality, horizontal exchange pasting, cancellation of
the source inverse-image compositor, and functoriality of compact-support pushforward.
The theorem's signature and its public import are unchanged.

Added two strictly smaller intermediate statements in separate modules. The compact-support
comparison statement has no vector bundle, frame, inverse-chart square, or integration
counit. The coefficient statement has no compact-support functor, exchange, or counit.
Their exact morphism equalities, source, and detailed proof plans are in their docstrings
and new nodes. The main proof uses both equations and proves the intervening exchange
pasting and naturality calculation in Lean. Added only private proof imports to the item.
No existing dependency module, definition, statement, attribute, or public import changed.

All three delivered modules compile through lcompile.py within the 60-second limit;
the completed item compiles cleanly in 15.6 seconds. The two new modules emit only
their declared theorem-hole warnings.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.vectorIntegration_restricted_chart_transport`
(node `lem-amb-vector-integration-restricted-chart-transport`) by decomposition. The item
module has zero remaining holes. This is a decomposition, not a net hole reduction: one
original hole closed and two new holes added, for a net change of minus one in holes closed.

The two remaining holes are exactly:

- `AlgebraicGeometry.Etale.affineTraceUnitCompactComparison_baseChange`
  (`lem-amb-affine-trace-unit-compact-base-change`), in
  `Sheaf.AlgebraicGeometry.AffineTraceUnitCompactBaseChange`.
- `AlgebraicGeometry.Etale.vectorIntegration_restricted_chart_coefficient`
  (`lem-amb-vector-integration-restricted-chart-coefficient`), in
  `Sheaf.AlgebraicGeometry.VectorIntegrationRestrictedChartCoefficient`.

Both are whole public theorem proofs. There is no postponed data, private proof hole,
or additional axiom. The assembly uses the existing `affineLinearExchange_paste`; it does
not restate the original theorem as a new assumption.

## No longer needed

None. No imports, modules, or nodes were pruned. The original tensor and Tate coherence
steps remain dependencies of the coefficient-only statement, and the unbounded comparison
package remains a dependency of the compact-support-only statement. The original Cartesian
prefix and geometric restricted chart are retained. Neither the unit statement nor any
step of its prescribed route was bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction or definition repair was needed. The original plan correctly
separates compact-support comparison transport from coefficient transport, but these
specializations were not yet named Lean declarations. Existing exchange pasting does
supply the intervening geometric assembly and is now used directly.

The new equations were checked mathematically at zero rank, empty opens/bases, the zero
coefficient ring, and identity restriction. Their sources and targets agree with the
actual constructions: the coefficient equation ends on the affine tower over U, whereas
the compact-support equation begins after ordinary compact-support pushforward over V.
No extra orientation, frame, counit, or arbitrary comparison is assumed. Searches of
Mathlib, the adopted source library, project modules, and blueprint found no matching
specialization; topological trivialization pullback and underived scheme-module pullback
coherence have different categories and maps.

## New nodes

`lem-amb-affine-trace-unit-compact-base-change` isolates the comparison of tower exchange
with ordinary compact-support exchange at the affine Tate coefficient. Its proof plan
uses compatibility of the compact-support compositor and exchange, their bounded-below
restrictions, and naturality in the coefficient. It is a specialization of the original
plan's compact-support part, without any inverse-frame geometry.

`lem-amb-vector-integration-restricted-chart-coefficient` isolates the equality of the
successive and direct inverse-image coefficient comparisons. Its proof plan uses the
constant-unit composition identity, normalized Tate transport uniqueness/composition,
monoidal inverse-image composition, and the prescribed ordered tensor recursion. It
contains no compact-support calculation. No change records are necessary because no
existing shared interface changed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
