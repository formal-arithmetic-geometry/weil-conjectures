## What changed

Retired the zero-hole duplicate module
`Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux` in favor of
`WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux`.
The source theorem proves the identical conclusion without assuming `hBrown`.

Adapted the sole consumer,
`Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer`: changed its
private auxiliary import, cleared its retained `hBrown` parameter, and applied the
stronger source theorem to `C hC H hH`. Its complete signature and visibility stay
unchanged. A declaration-local unused-variable linter option acknowledges that the
preserved parameter is no longer needed. All source-library files remain untouched.

Reattached `lem-pc-brown-representability-universe-transfer-aux` to the source theorem,
recorded the stronger statement, its existing Brown dependency and the sole citer's
continued validity, and updated the parent node's proof description.
Change record: `coord/changes/V4-brown-universe-transfer-aux-retirement.md`.

## Proved and sorry left

Initial item holes: **0**. Holes closed: **0**. Holes added: **0**. Sorries left in the
packet: **none**. This is a retirement/interface repair, not a new proof or decomposition.
The source auxiliary and the adapted consumer already have complete proofs.

The baseline item and adapted consumer were compiled through `lcompile.py`.
Axiom probes for both declarations reported only `propext`, `Classical.choice` and
`Quot.sound`. The source proof therefore introduces no `sorryAx` dependency.

## No longer needed

Withdrawn module:
`Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransferAux`.
Removed its import from the sole consumer and replaced it with the adopted source module.
Its duplicate proof and private imports of triangulated equivalence transfer, compact
generation transfer, opposite triangulated functors and additive-group universe lifting
are removed with the module. Those mathematical dependencies remain needed by the
complete adopted source proof; none of their nodes or source modules is withdrawn.
The auxiliary node remains attached to that source proof and the parent still uses it.
No additional node or module is claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed auxiliary, but the current queue marks this
item `retire`, and the live module has zero holes. The adopted source theorem is stronger
than the conditional Sheaf twin: Brown representability is proved, so `hBrown` is no
longer an assumption. Its former DAG proof step was conditional on `hBrown`; the new
attachment records the actual proved Brown dependency.

`tools/downstream.py --uses` and direct searches find exactly one consumer. No current
claim or quarantine/rework row names it. The only DAG parent is the retained conditional
universe-transfer node. The unit's `realized` fields do not mention this auxiliary;
the equivalence-transfer argument is preserved in the source proof. Empty generating
families and independent universes are handled by that unchanged general source theorem.
No target statement, definition or source-library declaration is changed.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
