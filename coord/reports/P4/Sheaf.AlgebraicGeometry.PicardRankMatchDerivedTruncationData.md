## What changed

Restored the full quarantined implementation of
Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData. The old public import
Sheaf.AlgebraicGeometry.DerivedPullback is an empty withdrawn module. Replaced it
with WeilConjectures.AlgebraicGeometry.DerivedPullback and explicitly qualified
AlgebraicGeometry.derivedPullback.{u, w} in the statement and proof, retaining the
intended fixed functor on the supplied shared derived categories.

Restored the cluster's immediate consumers PicardBaseChangeStalkSurjective and
PicardRankMatchBaseChange verbatim from their quarantine archives. All three files
compiled together with lcompile.py --all: 30.3, 7.4 and 4.0 seconds respectively.
The root also passed an earlier single-file compile in 20.2 seconds.

The existing argument is retained: construct K as the derived direct image of G[0],
use ordinary universal ranks and proper-flat perfection, prove the prescribed
canonical derived comparison invertible by affine locality, transport connective
vanishing and fixed ranks through that comparison, and use the pinned degree-zero
mate equation for the specified ordinary base-change map. K and a remain explicit
constructions; no arbitrary witness replaces them. No target, definition, unit route
or source-library file changes.

Updated the root node's lean.statement to the verbatim qualified signature and
recorded the restoration. Its mathematical statement, proof, proof_deps and all
other dependency edges are retained. Change record:
coord/changes/P4-picard-rank-match-derived-truncation-restoration.md.

## Proved and sorry left

This is a zero-hole rework repair, not a new proof or decomposition. The preserved
complete proofs of the following declarations now compile in the restored files:

- AlgebraicGeometry.Scheme.picardRankMatch_derived_truncation_data
- AlgebraicGeometry.Scheme.picardRankMatch_baseChange_stalk_surjective
- AlgebraicGeometry.Scheme.picardRankMatch_baseChange

The root's private finiteLocallyFree_isFlatOver helper is also retained and complete.
Original holes: 0. Holes closed: 0. Holes added: 0. Holes remaining in the delivery: 0.
No result is split off. The delivery command performs the final axiom and consumer
checks before pushing.

## No longer needed

Removed the public import of the empty withdrawn
Sheaf.AlgebraicGeometry.DerivedPullback, replacing it with its current source module.
No mathematical dependency, declaration, DAG node, consumer or module is pruned.
The preserved proof uses the existing declared dependencies, so no alternate route
or new intermediate theorem is needed. The search commands (grep, LeanFinder and
Loogle) found only generic adjunction and degree-zero derived-functor ingredients.

## Where the brief, the DAG or earlier work was wrong

The queue entry has zero holes: the assignment is restoration after global-build
quarantine. The original archive's statement fails at five occurrences of
unqualified derivedPullback because its public import has been withdrawn. The
compiler recommends the current WeilConjectures import; the repair supplies it and
explicitly fixes the intended namespace and universes. No mathematical error in
the node or its argument was found. The zero object, rank zero, empty schemes, and
the dual choice remain covered by the same uniform argument.

Attempted restoration farther along the eighteen-consumer quarantine closure.
The private compile overlay failed before these consumers could compile because
its current ProperFlatDirectImagePerfectChart dependency also imports the withdrawn
Sheaf derived-pullback module (unknown derivedPullback at line 80 and
unknown derivedPullback_spec at line 119). A later overlay attempt stopped at
PicardSingleRankPerfectChart because ProperFlatDirectImagePerfectChart.olean was
unavailable. This is an independent existing dependency failure, not a consequence
of the restored root's interface. Those farther consumers and the attempted chart
edit are excluded from the delivery; their archives, nodes and dependency edges
remain intact. The three contiguous restored modules all compile together cleanly.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
