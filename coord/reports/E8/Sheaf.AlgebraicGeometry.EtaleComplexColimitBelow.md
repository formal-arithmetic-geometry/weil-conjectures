## What changed

Retired `Sheaf.AlgebraicGeometry.EtaleComplexColimitBelow`, as explicitly requested
by its entry in `coord/retire-items.tsv`. The existing upstream twin already supplies
`AlgebraicGeometry.Etale.etaleComplex_colimit_below` with exactly the same signature
and proof. Repointed `lem-weil-pbc-etale-complex-colimit-below` to that upstream module.
The duplicate is listed in `deleted.txt`; no upstream source is changed.

Change record: `coord/changes/E8-etale-complex-colimit-below-retirement.md`.

## Proved and sorry left

This is a retirement repair with zero initial holes: 0 of 0 sorries closed, 0 added,
0 split off, and no sorry left in the retired module. The retained upstream theorem
`AlgebraicGeometry.Etale.etaleComplex_colimit_below` is already fully proved.
Its proof evaluates the colimit degreewise, transports vanishing along inverse image
and the supplied isomorphisms, and applies `IsColimit.isZero_pt`.

The original Sheaf module compiled before retirement (3.0 s). Single-file checks through
`lcompile.py` passed for the unchanged upstream theorem (2.8 s),
`WeilConjectures.AlgebraicGeometry.EtaleComplexCoherentFiltrations` (52.8 s), and
`WeilConjectures.AlgebraicGeometry.EtaleComplexUniformPages` (50.9 s), with no warnings.
The upstream theorem's `#print axioms` reports exactly `propext`, `Classical.choice`
and `Quot.sound`. Validation copies are confined to `scratchpad/` and are not delivered.

## No longer needed

The whole duplicate module `Sheaf.AlgebraicGeometry.EtaleComplexColimitBelow` and its
imports are no longer needed. No mathematical dependency or DAG node is pruned:
the two parent nodes still need the same lower-bound theorem, now provided upstream.
No new imports are introduced. Searches of `lean/` and `quarantine/` find no remaining
imports of the duplicate, and `tools/downstream.py` reports zero downstream modules.
The register's former Sheaf consumers have already been retired; the upstream
`EtaleComplexUniformPages` and `EtaleComplexCoherentFiltrations` both import the twin.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open proof, but the item is a registered retirement
repair and contains zero sorries. The node's Lean attachment was stale: it still named
the duplicate although current consumers already use the upstream copy. The retirement
inventory's old consumer list is also stale. The statement, mathematical proof, parent
DAG dependencies and unit route require no changes. No new nodes are introduced.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
