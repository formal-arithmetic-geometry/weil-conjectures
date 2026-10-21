## What changed

Restored Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart from the
quarantine path recorded in coord/rework.tsv. Replaced its public import of the
withdrawn Sheaf.AlgebraicGeometry.DerivedPullback with the adopted module
WeilConjectures.AlgebraicGeometry.DerivedPullback, as recorded on def-pc-derived-pullback.
The theorem statement, all proof bodies, docstrings and remaining imports are preserved.
The original source failed with unknown derivedPullback and derivedPullback_spec;
the repaired module compiled cleanly in 24.1 seconds through lcompile.py.

The existing node attachment and proof plan still match the restored proof:
ordinary rank normal form, an affine Cech model, its K-flat derived-pullback
comparison, and the actual zero object for the empty-test alternative. No node changes
or new mathematical results are necessary. The archived direct consumer
PicardUniversalSingleRankLocusFinitePresentation applies the unchanged chart theorem.

Change record: coord/changes/N2-picard-unrestricted-perfect-chart-restoration.md.

## Proved and sorry left

This is a zero-hole quarantine repair, not a new hole closure. The archive contains
zero sorry occurrences and the restored module contains zero. Holes closed: 0.
Holes added: 0. Split off: 0. No sorry declarations remain in this delivery.

The complete proof of
AlgebraicGeometry.Scheme.exists_picardSingleRankUnrestrictedPerfectChart is restored,
with its six proved private helpers freeZero_isZero, rank_of_isEmpty,
zero_rank_one_iff, zero_isPerfect, zero_tensor_vanishes, and derivedPullback_zero_isZero.
The delivery preserves all existing dependency theorems rather than replacing any by holes.

## No longer needed

Removed the obsolete public import Sheaf.AlgebraicGeometry.DerivedPullback, which now
contains no declarations; use the adopted source module instead. No live mathematical
node, theorem or module is pruned, and all eight declared proof dependencies remain used.
The chart is still required by the archived parent and its DAG proof; its absence from
lean/ does not constitute withdrawal. No deleted.txt is supplied.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a sorry-bearing item, but this assignment is the
zero-hole restoration explicitly listed in coord/rework.tsv. The old archive still
imported the retired derived-pullback twin. Its node already points at the adopted API,
so that source import alone needed correction. No statement dispute or change of
mathematical argument was found. The ordinary rank normal form and affine Cech model
already provide the shortest stated route; searching did not identify a shorter
Mathlib replacement. No further splitting is needed.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
