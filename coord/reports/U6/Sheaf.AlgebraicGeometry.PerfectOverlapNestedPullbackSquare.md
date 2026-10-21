## What changed

Restored the quarantined Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare
as a public adapter to WeilConjectures.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare.
Preserved the existing public Sheaf.PerfectOverlapStageEquivalence helper import and
reattached lem-pc-perfect-overlap-nested-pullback-square to the adopted source module.
The theorem and explicit comparison declaration blocks are byte-identical in the archive
and the adopted source. No source-library file, signature, attribute or body was changed.

Change record: coord/changes/U6-perfect-overlap-nested-pullback-source-adapter.md.

## Proved and sorry left

This is a zero-hole restoration and duplicate-definition repair: 0 of 0 holes closed,
0 holes added, 0 split off, and no sorry left in the delivered module. The source theorem
AlgebraicGeometry.perfectOverlapNestedRestrictedMaps is already proved; the source
AlgebraicGeometry.perfectOverlapNestedPullbackSquare is explicit constructed data.
The restored adapter compiled successfully through lcompile.py (2.4 seconds).

## No longer needed

The duplicate Sheaf declarations and their obsolete local reducibility commands are no
longer needed. No import was removed: the previous public helper API is preserved, and
the canonical source module is added publicly. No mathematical dependency, DAG node or
module is pruned. The original node proof and dependency lists still describe the exact
source construction. The assigned module is restored, not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned archived module has zero sorry occurrences, not an unfinished mathematical
proof. Restoring it unchanged fails at line 25: failed to set local irreducible because
derivedPullback is already irreducible. The adopted source already contains both of the
archived declarations with identical signatures and bodies; restoring second definitions
would violate one definition per notion. The node attachment previously named the
quarantined duplicate instead of the source declaration. Its mathematical statement,
proof steps and unit route need no change. Quarantined consumers were read and retained;
zero active importers was not taken as evidence that this mathematics was unused.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
