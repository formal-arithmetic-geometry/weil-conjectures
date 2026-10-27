## What changed

Decomposed IntegralStratumCharts.integral_stratum_chart_restrictions into geometric chart
existence and functorial compatibility. The original theorem combines these strict substatements,
proves preservation of constructibility directly from integralOperations_preserve_constructible,
and obtains the normalized comparison from integralPullback_completedComparison. Global unit
hypotheses are transported to stalks and residue fields by actual ring homomorphisms.

Extracted the existing definitions and structures, with their original names, signatures,
visibility and bodies, to IntegralStratumChartRestrictionsData. The original module publicly
imports it; both child modules publicly import it. The five original public imports are retained
there. This extraction breaks the otherwise circular dependency of child statements on their
parent's data. It was not a response to a timeout.

Repair of return 0bf2381b027: rebuilt the extraction from the restored current source
(c654f059d86, build 2026-10-25T09:43:02Z), then reapplied the proof. Exact text comparison
confirmed all thirteen data declarations and the original theorem signature agree with the
retained packet; only the data node docstring pointer differs. Refreshed the parent node from
its current record, preserving its non-proof metadata. The data module contains zero sorry.
Validation: the repaired data and both component modules compiled remotely (45.7, 28.2 and
28.9 seconds reported). The main-module compile could not start: stdbuf failed to create its
/tmp directory with No space left on device (exit 125). Delivery preflight is attempted next.
Change record: coord/changes/J7-integral-stratum-chart-data-extraction.md.

## Proved and sorry left

Closed the one original hole:
WeilConjectures.IntegralStratumCharts.integral_stratum_chart_restrictions
(node lem-a1-integral-stratum-chart-restrictions). Its constructibility conjunct is proved from
an existing declaration; its comparison witness is obtained from the existing comparison theorem.

Added two holes, each the whole proof of a named public theorem:

- WeilConjectures.IntegralStratumCharts.integral_stratum_charts
  (lem-a1-integral-stratum-charts-existence).
- WeilConjectures.IntegralStratumCharts.integral_stratum_pullback_functorial
  (lem-a1-integral-stratum-pullback-functorial).

This is a decomposition, not a claim to have discharged the underlying chart or functorial
arguments. There are zero holes in the assigned module and two across the delivery, net -1.
The two children are strictly smaller than the original conjunction: neither asserts the
other's conclusion or preservation of constructibility. Their docstrings give the complete
recorded source argument. Empty schemes/strata, zero complexes, zero scalars and arbitrary
cohomological intervals are retained; no nonemptiness or flatness assumption is added.

## No longer needed

Removed these unused proof imports from the assigned module:
Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat,
Sheaf.CategoryTheory.StrictRoosAdditiveComparison,
Sheaf.CategoryTheory.LocalizedModuleExactForSystems,
Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction,
Sheaf.Targets.SliceRestrictionStrictDerivedLimit,
Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation.
Their mathematical statements remain needed by the chart child, whose proof steps retain the
original dependencies. ConstructibleSheaf.Pullback moved to the data module, where pulledStrata
uses it. The five original public imports moved to the publicly imported data module.
No mathematical node/module is pruned globally: every original proof dependency remains either
used directly by the parent or in the child proof plans. No library declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies do not directly expose the Charts record or the scalar/triangle
compatibility assertion, so those are separate glue arguments. They are now explicit items.
The constructive preservation conjunct does fit integralOperations_preserve_constructible and
needs no new statement. The public data and original theorem's statement were retained exactly.
The first delivery used a base before the current source was restored and was returned by
the landing source gate. This packet starts from that restored file and applies the actual
decomposition to it. Its complete data block and theorem signature were compared exactly.
The earlier zero-consumer observation is obsolete: the current file has one direct consumer,
ConstructiblePullbackTExact, and 918 transitive consumers. The direct consumer mentions none of
the relocated names; public re-export preserves all names and the original public imports.
No consumer adaptation or withdrawal is required.

## New nodes

def-a1-integral-stratum-chart-restrictions-data owns the existing data declarations extracted
unchanged to the new data module, including Charts.pulledStrata. It has no proof hole.

lem-a1-integral-stratum-charts-existence carries the geometric and exact-restriction chart
construction, including actual pulled-back covers and the normalized finite comparison square.
Its proof is the original steps 1--8, with all their dependencies retained.

lem-a1-integral-stratum-pullback-functorial carries only the additive, scalar and triangulated
part for a supplied normalized comparison. Its proof is original step 9; the parent's existing
comparison theorem supplies that record. Neither new theorem repeats the assigned conjunction.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
