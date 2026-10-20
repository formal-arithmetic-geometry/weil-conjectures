## What changed

Retired the zero-hole Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction,
which the current queue marks `retire`. Its current consumer count is zero.
The public source-library fixed-rank pullback API already replaces the private
rank helpers. The stronger, proved upstream synchronization theorem supplies the
old public statement directly. Updated the old node's Lean attachment and proof
route to that theorem, preserving its mathematical statement. No upstream file is
changed. Change record:
coord/changes/retire-picard-universal-rank-match-conjunction.md.

## Proved and sorry left

The item originally contains zero sorries; holes closed: 0; holes added: 0;
sorries left: none; split off: none. This is a retirement, not a newly closed hole.
A sandbox scratch check specializes the existing upstream
AlgebraicGeometry.Scheme.picardUniversalRankMatch_of_singleRankMatch_without_unit
to the exact retired signature. The upstream theorem and the two public fixed-rank
pullback lemmas are checked with #print axioms through lcompile.py.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction.
Removed its unused declaration picardUniversalRankMatch_of_singleRankMatch and
private tensorIso, tensorRank, tensorRankComp, rankOnSmallerOpen,
referenceRankOnSmallerOpen, nonempty_of_unit_iso. No source-tree declaration is removed.

All five imports disappear with the retired module:
WeilConjectures.AlgebraicGeometry.PicardUniversalSingleRankMatch,
WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch,
WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction,
WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank,
and WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank.
These modules are not claimed globally unnecessary.

The old node's direct proof dependencies def-pc-module-pullback,
def-sc-picard-universal-rank-match, def-sc-picard-universal-single-rank-match,
lem-pc-module-pullback-adjunction, lem-pc-module-pullback-identity-composition,
and lem-sc-finite-locally-free-stalk-finrank are replaced by the already existing
lem-sc-picard-universal-rank-match-synchronization. They may remain needed by
other nodes and by the stronger theorem. No DAG node is deleted.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a holed module, but this is a zero-hole
retirement item. The queue and retire-items.tsv retain three obsolete consumers:
Sheaf.AlgebraicGeometry.PicardBaseChangeStalkFinrankEq,
Sheaf.AlgebraicGeometry.PicardSingleRankSourceLocal, and
Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank.
All three files are already absent from the current source tree, and neither Lean
root imports the retired module. No forced adaptation is needed. The upstream
conjunction module now exposes the fixed-rank API and the separate synchronization
module already proves the stronger theorem. The unit's realized statement and step
lists are empty; no fixed blueprint route is bypassed.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
