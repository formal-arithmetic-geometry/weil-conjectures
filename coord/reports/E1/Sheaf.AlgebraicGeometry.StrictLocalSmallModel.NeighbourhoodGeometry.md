## What changed

Restored Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry from its
coord/rework.tsv quarantine source. Replaced four obsolete diagram references inside
StrictLocalNeighbourhoodGeometry.smallModelFirst with the current upstream
Scheme.strictHenselizationDiagram. The final-functor inverse coprojection equation then
proves the same canonical small-model leg formula. The whole module compiles through
lcompile.py in 7.2 seconds. All five declaration signatures, three definition bodies,
attributes and both public imports are preserved verbatim from the archive.

Updated the existing geometry-transport node's proof description to identify the full
upstream diagram and its small ring-written whiskering. The mathematical route and
proof dependencies are preserved. The unit's realized route is untouched.

Change record: coord/changes/E1-neighbourhood-geometry-diagram-repair.md.

## Proved and sorry left

This is a zero-hole repair: 0 original sorries, 0 closed, 0 added, 0 remaining;
0 statements split off. No decomposition is claimed.

The restored declarations are AlgebraicGeometry.Etale.strictLocalSmallModelPullbackIso
and AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelLegs,
smallModelIsLimit, smallModelOver and smallModelFirst. Every proof is complete.
The assigned compiler error in smallModelFirst is repaired.

## No longer needed

None. Both public imports are used, all declared proof dependencies remain needed,
and no node or module is withdrawn. The quarantine archive remains preserved.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean because it was quarantined, not withdrawn. Its archived
proof used the removed smallStrictHenselizationDiagram name for the full upstream
affine-neighbourhood diagram. Current upstream smallStrictHenselizationColimitIso uses
strictHenselizationDiagram. The small ring-written diagram remains
strictHenselizationAffineDiagram; these two diagrams are not interchanged.

The live downstream tool cannot census a quarantined module. The change record instead
lists all direct consumers found in both live and quarantine source trees. Their API
remains identical and none requires an edit. The current blueprint no longer has the
historical sk-prop-h2 directory named by the unit record; the authoritative existing
unit record and its realized route are preserved.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
