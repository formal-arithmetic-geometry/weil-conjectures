## What changed

Replaced the proof of `exists_picardUniversalRankMatchLocus_core_rank` by specialization
of the existing proved `exists_picardUniversalRankMatchLocus_finitePresentation_core`:
keep its representative, immersion and universal property, discard local finite presentation.
The original hO assumption, every public import, all declaration signatures, and the
core-condition abbreviation remain unchanged. `picardUniversalRankMatchCoreCondition_iff`
remains proved by reflexivity. The rank node's proof, proof_deps and proof_origin now
follow this shorter route; the compatibility node needs no change.

The live C3 version compiled before editing. The new proof and the unchanged quarantined
direct consumer `PicardUniversalRankMatchLocusCore` compile together. Import-direction
checking confirms no cycle. The delivery preflight performs its independent compile and
axiom checks. Change record: `coord/changes/B2-picard-core-rank-reuse-finite-presentation.md`.

## Proved and sorry left

Actual item hole count: zero before, zero after. Holes closed: none. Holes added: none.
No decomposition and no split-off theorem. Both existing theorems remain fully proved:
`AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core_rank` and
`AlgebraicGeometry.Scheme.picardUniversalRankMatchCoreCondition_iff`.
There is no sorry left in the item or added elsewhere by this delivery.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus`
and `WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatchSynchronization`.
Synchronization remains needed transitively by the reused construction; its node and
upstream theorem are not withdrawn. The old conjunction node is no longer a direct
dependency of this item; its synchronization content remains used through the stronger result.

The following complete modules leave this item's import closure:

- `Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus`
  (`lem-sc-picard-universal-single-rank-locus`);
- `Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart`
  (`lem-sc-picard-single-rank-perfect-chart`);
- `WeilConjectures.AlgebraicGeometry.PicardReferenceRankNeighbourhood`
  (`lem-sc-picard-reference-rank-neighbourhood`).

Their separate structure-unit-dependent rank-neighbourhood route is unnecessary because
the existing unrestricted construction already proves the stronger conclusion. The new
private import reaches the unrestricted perfect-chart and finitely presented single-rank
locus construction instead. Shared dependencies, including proper flat perfect charts,
lowest-cohomology loci, and synchronization, remain needed. No module or declaration is
deleted, in particular none in the adopted source library.

## Where the brief, the DAG or earlier work was wrong

The rework queue still presents the module as requiring restoration, but the current source
already contains C3's compiling 2026-10-22 repair. The archived file calls a retired theorem;
C3 replaced that call. This delivery preserves that correction and removes the duplicate
proof branch rather than claiming a hole closure or submitting an unchanged restoration.
The DAG's previous plan was valid but longer than necessary given the existing stronger
construction. No target statement, definition meaning, or blueprint unit route changes.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
