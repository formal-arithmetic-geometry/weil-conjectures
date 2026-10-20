## What changed

Retired Sheaf.AlgebraicGeometry.Modules.DeterminantSplitChartComparison, as assigned
in coord/retire-items.tsv:274. Its theorem is already proved in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitChartComparison.
The node now attaches to that canonical upstream declaration. No upstream source changed.

Adapted the only direct consumer,
Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective: replace its private
chart import with the official module, add a private presheaf-compatibility import,
and transport the middle and tensor comparison conclusions to its unchanged legacy
types. Unfolding exteriorPower before rewriting the tensor comparison transports
its dependent codomains together. All consumer signatures and public imports stay
identical. Updated its node to record this use of the existing compatibility theorem.

Change record: coord/changes/retire-determinant-split-chart-comparison.md.
The adapted consumer compiles without errors or warnings in 6.2 seconds.
Searches through msearch.py and direct source inspection confirmed the upstream
match; Mathlib search gives tensor-map bijectivity but no competing chart theorem.
The unit route and all mathematical hypotheses and conclusions are preserved.

## Proved and sorry left

Assigned retirement: zero existing holes, zero holes closed, zero added, zero left.
The retired theorem determinant_split_chart_comparison and all its private helpers
were already proved. The upstream realization is also proved. The adapted consumer
is sorry-free, including determinant_split_linear_maps_locally_bijective and all
its helpers. No new theorem or split-off obligation is introduced.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.DeterminantSplitChartComparison.
Removed its private import from the sole direct consumer; the official module
replaces it. The upstream theorem retains the common-chart node and its proof
route. No mathematical node is withdrawn.

The chart node itself no longer needs lem-sc-exterior-sheaf-presheaf-upstream-comparison
or lem-sc-exterior-sheaf-upstream-comparison: the canonical upstream theorem uses
canonical exterior constructions directly. The first remains needed by the adapted
consumer and is recorded in its proof dependencies. The second is not needed by
either the upstream chart proof or this consumer adaptation; it remains in the
library for other callers. No other dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving holes, but the queue and retirement list assign
this zero-hole duplicate retirement. The legacy and canonical exterior presheaves
are propositionally equal, not definitionally equal. The tensor comparison cannot
be migrated by rewriting its unit arguments alone because the tensor sheaves also
depend on these presheaves. Unfolding the canonical sheaf exteriorPower before the
proved presheaf rewrite resolves this without changing any statement or definition.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
