## What changed

Retired `Sheaf.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen` in favor of
`WeilConjectures.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen`, as assigned by
`coord/retire-items.tsv` and the human's retirement instruction in
`coord/changes/retire-sheaf-twins-20261020.md`.

Updated the `lean` attachment of `lem-sc-finite-free-map-iso-locus-basic-open` to the
upstream module and its actual signature. The theorem name and conclusion agree;
upstream omits the unused `hU : IsAffineOpen U` argument. Applying the upstream theorem
with the remaining arguments proves the entire old statement, including arbitrary
finite ranks, rank zero, and the empty open. The node's mathematical statement and
proof route remain unchanged. No upstream file, definition, or target is modified.

Change record: `coord/changes/D8-retire-finite-free-map-iso-locus-basic-open.md`.

## Proved and sorry left

This is a retirement repair with zero initial holes. Holes closed: 0; holes added: 0;
split off: 0; holes left: 0. No new theorem or definition is introduced.
The retained declaration is
`AlgebraicGeometry.Scheme.Modules.moduleMapIsoLocus_inter_eq_basicOpen_of_free` in
`WeilConjectures.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen`.

A sandbox scratch example checks the complete old signature by applying the upstream
theorem, and prints the upstream theorem's axioms. It compiles cleanly in 2.0 seconds and reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The unchanged upstream compactness consumer
also compiles cleanly in 3.1 seconds. `tools/downstream.py` reports zero downstream
modules for the withdrawn Sheaf module. Scratch checks are not delivered.

## No longer needed

Withdrawn module:
`Sheaf.AlgebraicGeometry.FiniteFreeMapIsoLocusBasicOpen`.
Its duplicated public theorem and eight private proof helpers are no longer needed.
The existing node is retained and attached to upstream, not deleted.

A current scan of all `lean/Sheaf` and `lean/WeilConjectures` files finds no imports of
the withdrawn module. The listed former consumer,
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusCompact`, has already been retired.
Its upstream counterpart already imports the upstream basic-open module and calls the
theorem without the removed affine argument. No consumer adaptation is required.
The old module's six imports disappear with its withdrawal; all necessary proof
imports remain in the upstream theorem's module. No dependency node is declared
unnecessary for the retained determinant proof.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with an open proof, but the current queue
assigns this module as a retirement item. Its proof was already complete. The
retirement table's consumer list is stale: the sole listed Sheaf consumer no longer
exists, and its upstream replacement already uses the generalized theorem correctly.
The DAG attachment still named the duplicate and included the removed affine binder;
this delivery corrects that attachment without changing the node's affine statement.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
