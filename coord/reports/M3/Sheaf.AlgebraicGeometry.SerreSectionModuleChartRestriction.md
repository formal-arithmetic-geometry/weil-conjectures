## What changed

Retired Sheaf.AlgebraicGeometry.SerreSectionModuleChartRestriction, the depth-zero
retirement item listed in coord/retire-items.tsv. Its upstream twin already proves
the same conclusion without hd, hb and he. Switched the one consumer,
Sheaf.AlgebraicGeometry.SerreSectionModuleCharts, to the upstream proof import and
removed those three arguments at its only call site. Redirected the existing DAG
node's Lean attachment to the upstream theorem, with its exact signature.

Change record: coord/changes/retire-serre-section-module-chart-restriction.md.
No upstream file, target statement, consumer signature or definition changes.

## Proved and sorry left

Zero original holes; zero holes closed; zero holes added; zero split off.
AlgebraicGeometry.Proj.serreSectionModuleChartRestriction was already proved in
both copies. Its upstream proof is reused. The adapted consumer theorem
AlgebraicGeometry.Proj.serreSectionModuleCharts retains a complete proof.
No delivered declaration contains sorry.

Validation: the adapted consumer compiled through lcompile.py in 4.6 seconds.
Its unmodified transitive consumer CoherentProjRepresentation also compiled
against the adapted consumer in 5.8 seconds (temporary sandbox source removed).
An import-closure scan of its 143 project modules found no environment
containing both a Sheaf module and its upstream twin. The old and new restriction
modules have identical dependency import lists.

## No longer needed

The duplicate module Sheaf.AlgebraicGeometry.SerreSectionModuleChartRestriction is
withdrawn through deleted.txt. Its sole consumer drops that private import and
imports WeilConjectures.AlgebraicGeometry.SerreSectionModuleChartRestriction.
The node lem-sc-p1-serre-section-module-chart-restriction remains needed and now
points to the upstream twin. Its proof dependencies are unchanged. No other node
or module is pruned. The upstream twin has exactly the same imports as the copy;
the replacement introduces no new transitive dependency besides the twin itself.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes holes, but this queue item is a retirement
with zero holes. The explicit retirement record supplies the actual task.
The DAG's old Lean signature includes hd, hb and he, whereas the upstream theorem
needs none of them. The unchanged mathematical node statement follows from that
stronger theorem; only its attachment changes.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
