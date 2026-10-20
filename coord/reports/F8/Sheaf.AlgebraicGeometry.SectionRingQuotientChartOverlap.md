## What changed

Retired the duplicate module `Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlap`
using `deleted.txt`, as assigned by `coord/retire-items.tsv`. Reattached
`lem-sc-section-ring-quotient-chart-overlap` to the already proved adopted theorem
`AlgebraicGeometry.Scheme.Modules.sectionRing_quotient_charts_overlap` in
`WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlap`.
No source-library file, target statement, consumer, or public interface changes.
The change record is
`coord/changes/retire-section-ring-quotient-chart-overlap-F8.md`.

Validation: a scratch theorem with the complete former signature applies the upstream
theorem directly and compiles through `lcompile.py` in 1.7 seconds. Both axiom prints
list exactly `propext`, `Classical.choice`, and `Quot.sound`. An unchanged scratch
copy of the upstream compatible-charts consumer compiles in 1.6 seconds. The source-wide import search finds no current importer of the
withdrawn Sheaf module; the compatible-charts consumer already uses the upstream
module.

## Proved and sorry left

The assigned module had zero holes at the delivery base: zero closed, zero added,
and zero split off. Retirement preserves the complete upstream proof, so no sorry
remains in any delivered or retained theorem.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.SectionRingQuotientChartOverlap`. Its imports
are removed with it: `WeilConjectures.AlgebraicGeometry.InvertibleSectionRing`,
`WeilConjectures.AlgebraicGeometry.Ample`,
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`,
`WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapBase`, and
`WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapSheaf`.
These dependencies remain needed by the upstream proof; they are not withdrawn. No
mathematical dependency node is pruned: the upstream theorem carries the same
statement and the unit route remains intact. No consumer import is removed because
all current consumers already use the adopted source module.

## Where the brief, the DAG or earlier work was wrong

The generic brief described a proof item, but the current retirement census and queue
classify this module as a duplicate retirement. The adopted source theorem already
closes the node, so recreating a Sheaf proof would preserve an unnecessary duplicate.
No statement or definition repair is needed.


The retirement table labels the signatures DIFFERENT, but their only textual binder
difference is the spelling of the universally quantified positive-degree assumption.
The direct specialization checks the whole old statement, including empty opens,
without adding any hypothesis. The DAG parent
`lem-sc-ample-proj-compatible-quotient-charts` already points to
`WeilConjectures.AlgebraicGeometry.AmpleProjCompatibleCharts`, which imports and
applies the retained theorem. Reattaching this node preserves that dependency; the
unit `sk-thm-curveestimate` realizes its statement at `thm-sc-proper-cohomology` and
no unit step is bypassed. The current rework and F8 returns files have no row for
this item. The quarantined-source import scan also finds no importer.

LeanFinder returned general Proj chart lemmas, and Loogle returned `Scheme.Hom.ext`;
neither supersedes this invertible-module comparison. The local library search
finds its exact proved upstream twin, which supplies the replacement.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
