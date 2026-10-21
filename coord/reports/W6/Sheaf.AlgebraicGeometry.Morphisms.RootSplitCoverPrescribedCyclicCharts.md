## What changed

Retired `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts`
in favor of its already proved upstream counterpart. The sole direct consumer,
`Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorPrescribedPuncturedRootChart`,
privately imports the upstream module and calls its theorem without the obsolete
`hgz` hypothesis; the now unused transport proof is removed. Its public signature
is unchanged; the retained `hy` hypothesis is explicitly referenced to keep the
unused-variable linter clean. Reattached `lem-sbc-root-split-cover-prescribed-cyclic-charts` to the
upstream declaration and updated the parent's proof description. The mathematical
classification and unit route are preserved.

Change record: `coord/changes/retire-root-split-cover-prescribed-cyclic-charts.md`.

Return repair for reviewer C-e09f0, returned head `e09f095fb54`: retained the
reviewed migration and compared it with the current shared sources. The source
declarations, consumer signature, sole direct import, and two affected DAG nodes
still match the assumptions of that migration. The item is present in `lean/`,
has no quarantine rework row, and remains the retirement assigned to W6. Checked
the current DAG parents and unit record as well as Lean and quarantine imports;
the upstream attachment preserves the mathematical dependency. The consumer
passes the repair retry’s fresh single-file server compile through
`LCOMPILE_NO_LOCAL=1 lcompile.py --all` (exit 0, 3.6 seconds, no warnings). The delivery tool rebuilds this packet
on current `origin/sheaf-dag` and runs the server checks before pushing.

## Proved and sorry left

The assigned retirement has zero holes: proved 0 of 0 sorries; added 0; split off 0.
`AlgebraicGeometry.Scheme.root_split_cover_prescribed_cyclic_charts` remains proved
in the upstream module. The adapted
`AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_prescribed_punctured_root_chart`
retains its complete proof. No sorry remains in a delivered Lean module.

## No longer needed

Removed the consumer's private import of
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts` and withdrew
that duplicate module through `deleted.txt`. The corresponding DAG node remains,
attached to `WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverPrescribedCyclicCharts`.
No mathematical dependency node is pruned: the cyclic chart model and regular
divisor base-change lemmas remain needed by the upstream proof. No other module
is withdrawn. The consumer no longer needs the proof that g belongs to z.asIdeal.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a deep sorry chain, but the assigned module
is already proved and the current queue marks it as a retirement. Its historical
PROOFDIFF_UNSAFE classification warns about combining distinct supporting copies;
the current Sheaf and upstream modules both import the same upstream supporting
modules, so replacement introduces no extra supporting copy. The only theorem
interface difference is the Sheaf copy's unused divisor-point hypothesis. The
upstream theorem is stronger and supplies exactly the required conclusion. The
node's divisor-point hypothesis is retained in its natural-language statement;
the stronger upstream Lean attachment proves it as a special case.

The returned delivery had passed mathematical review. Its landing failed while
reading the unrelated `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison`
source. The requested repair is to rebuild the retained packet on current
`sheaf-dag`, compile it on the server, and deliver again; it does not call for
restoring, withdrawing, or changing that unrelated module.

The previous retry could not deliver because its cache lookup stalled before
preflight. This retry preserves the reviewed Lean migration, rechecks its source
and dependency assumptions against current `sheaf-dag`, and runs the required
server compile and delivery anew. The current cache implementation includes a
launcher-owned correction for the former serialized cache wait. No launcher
script or lock file was changed, and no cache or delivery check was bypassed.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
