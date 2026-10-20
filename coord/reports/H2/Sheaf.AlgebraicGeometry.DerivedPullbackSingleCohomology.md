## What changed

Withdrew the Sheaf compatibility duplicate `Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology`.
The adopted source module `WeilConjectures.AlgebraicGeometry.DerivedPullbackSingleCohomology`
retains the complete theorem and proof. The assigned module had zero textual holes; this
repair removes the redundant module and lets the rework/retirement machinery install its
empty withdrawn stub. No consumer imports the Sheaf path, and the source theorem remains
publicly available through the adopted source root.

## Proved and sorry left

The assigned module had zero sorries before this delivery and zero sorries are added.
There are zero holes closed and zero split off. The theorem attached to
`lem-pc-derived-pullback-single-cohomology` remains fully proved in the adopted source
module; its proof and statement are unchanged.

## No longer needed

The withdrawn compatibility module and its duplicate public import are no longer needed.
No proof dependency or DAG node is removed: the source module continues to provide the
complete theorem, and the source library's own imports remain unchanged. The quarantine
archive is preserved by `coord/rework.tsv`; `deleted.txt` records only the live Sheaf path.

## Where the brief, the DAG or earlier work was wrong

The queue still listed this module after an earlier restoration delivery, even though the
current retirement inventory marks the Sheaf copy for withdrawal and the adopted source
already contains the complete theorem. The retirement entry classifies the twins as
having different dependency closures, so this delivery withdraws only the redundant Sheaf
path and leaves all source declarations intact. Direct import and declaration searches
show zero users of the Sheaf module.

Change record: `coord/changes/H2-derived-pullback-single-cohomology-retire.md`.

## Second reading by H2

No second reading by a worker is required for this withdrawal; the independent stage-3
review checks the zero-user condition and the unchanged adopted source theorem.

## New nodes

None.
