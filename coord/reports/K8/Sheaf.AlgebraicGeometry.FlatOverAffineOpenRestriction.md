## What changed

Retired Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction as a duplicate of
WeilConjectures.AlgebraicGeometry.FlatOverAffineOpenRestriction, and reattached
lem-pc-flat-over-affine-open-restriction to its existing complete upstream theorem
AlgebraicGeometry.isFlatOver_affineOpenRestriction. The theorem's full signature
and mathematical meaning are identical. Updated the node's final proof step to
name the upstream IsFlatOver.of_iso transport. No source-library file is edited.

The current source is a listed retirement item, already proved rather than a
remaining proof obligation. Both parents already import the retained upstream
module. Their mathematical dependencies on this node stay intact; changing the
child's attachment supplies the existing replacement proof to both parents.
This repairs the duplicate attachment rather than merely recompiling it.

Verification through lcompile.py:

- Original Sheaf module: compiled in 4.2 seconds, zero holes.
- Retained upstream module: compiled in 3.8 seconds, zero holes.
- Exact old theorem signature, proved by applying the upstream theorem: compiled
  in 3.0 seconds. #print axioms reports only propext, Classical.choice, Quot.sound.
- Unchanged CanonicalModuleBaseChangeAffineLocality: compiled in 11.6 seconds.
- Unchanged ProperFlatCohomologyData: compiled in 15.7 seconds.

Change record: coord/changes/flat-over-affine-open-restriction-upstream.md.
Searches were executed through msearch.py (leanfinder, loogle, grep), supplemented
by repository searches. The exact existing theorem is the shortest route.

## Proved and sorry left

Original holes: zero. Holes closed: zero. Holes added: zero. Split off: zero.
No remaining sorry in the withdrawn item or its retained upstream replacement.
AlgebraicGeometry.isFlatOver_affineOpenRestriction was already completely proved;
this delivery retires its duplicate and records the actual proof location. The
replacement proof has only the three permitted axioms. No proof-progress claim
is made for earlier work or for parent theorems' other dependencies.

## No longer needed

The module Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction is withdrawn via
deleted.txt. Its private flatOver_morphismRestrict, flatOver_postcomp_iso and
flatOver_of_iso helpers are removed with the duplicate file. The retained
upstream theorem uses its own proved helpers and the public IsFlatOver.of_iso.
No declaration is removed from WeilConjectures.

The withdrawn file's public imports of
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic and
WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps disappear with it;
both are still required by the retained upstream theorem. No mathematical node
is pruned. Both parent dependencies and the unit route are preserved.

There are no current Lean importers of the Sheaf copy, including quarantined
sources. The only DAG attachment to it is the migrated node. The two DAG parents
lem-pc-canonical-module-base-change-affine-locality and
lem-pc-proper-flat-cohomology-model-data already attach to upstream consumer
modules, both importing the exact replacement. The source-library umbrella also
already imports the replacement. No consumer adaptation is necessary.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a repeatedly split proof obligation, but the current
item has no sorry and compiles. coord/retire-items.tsv lists its retirement;
coord/rework.tsv and the group's return file have no repair entry for it.
The older retirement inventory called this pair DIFFERENT because the upstream
copy lacks a private helper and previously had incompatible dependency twins.
The current two files publicly import the same upstream definitions. Their
public theorem statements are identical, and both existing consumers already
use the upstream proof. Private helper differences therefore do not require
retaining the duplicate public declaration.

The existing node incorrectly pointed to the unused Sheaf copy. Reattaching it
preserves the mathematical assertion and all parent dependencies; it does not
withdraw mathematics merely because the old file has zero importers. No new
nodes, hypotheses, constructions, or axioms are introduced.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
