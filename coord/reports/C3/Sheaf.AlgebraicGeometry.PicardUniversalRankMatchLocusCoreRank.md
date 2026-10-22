## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardUniversalRankMatchLocusCoreRank.lean
from the quarantine path in coord/rework.tsv. Replaced its proof-only import of the
withdrawn Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction with
WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatchSynchronization, and
replaced the retired theorem call with
AlgebraicGeometry.Scheme.picardUniversalRankMatch_of_singleRankMatch_without_unit.
The original fibre-product construction, core-condition abbreviation, both theorem
signatures and all public imports remain unchanged. Added the module header and
updated the rank node proof text to identify the current synchronization theorem.

The unchanged archive fails compilation with an unknown identifier at the old call.
The restored module compiles cleanly through lcompile.py. The unchanged archived
direct consumer PicardUniversalRankMatchLocusCore compiled unchanged against the restoration (4.8 seconds); the item compiled in 6.2 seconds.
Import-direction checking permits the new private proof import. Consumer inventory
includes live and quarantined sources; see the change record
coord/changes/C3-picard-rank-core-upstream-synchronization.md.

## Proved and sorry left

This is a zero-hole quarantine repair: 0 holes before, 0 holes after, 0 closed and
0 added. No statements are split off. Both existing theorem proofs are retained:
AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core_rank
(lem-sc-picard-universal-rank-match-locus-core-rank), now using the current proved
synchronization theorem, and
AlgebraicGeometry.Scheme.picardUniversalRankMatchCoreCondition_iff
(lem-sc-picard-universal-rank-match-locus-core-compat), proved by reflexivity.
No sorry remains in the restored item and no other Lean source is delivered.

## No longer needed

Removed the proof import Sheaf.AlgebraicGeometry.PicardUniversalRankMatchConjunction,
which is already withdrawn. Its mathematical conjunction dependency remains needed:
lem-sc-picard-universal-rank-match-conjunction now records the upstream synchronization
theorem used here. No DAG dependency, parent, unit step or additional module is pruned.
The two single-image locus applications remain essential to the fibre-product proof.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, rather than present under lean/, and already has
zero holes. The archive still names the retired conjunction theorem, although the
current dependency node correctly points to the stronger proved upstream theorem.
Restoring that archive without adapting the call reproduces its compile failure.
The new theorem has the same conclusion and does not require hO; hO is retained
and used by both single-image locus applications. No weaker statement is substituted.

Read Stacks more-morphisms.tex, lemma-diagonal-picard-flat-proper (Tag 0BDP),
particularly its rank-stratum, two lowest-cohomology loci and fibre-product paragraphs.
The existing construction follows those paragraphs. The current synchronization
proof also handles empty fibres; empty test schemes remain vacuous. No new edge-case
hypotheses are introduced. The unit sk-prop-av-cube and all original dependency
attachments are preserved.

Searches: LeanFinder for the intersection of loci represented by immersions found
Mathlib immersion pullback instances; Loogle found pullback.lift and its projection
identities. Local rg found the current synchronization theorem and the parallel
finite-presentation core construction. The launcher grep search returned zero hits.
No new statements or nodes were needed.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
