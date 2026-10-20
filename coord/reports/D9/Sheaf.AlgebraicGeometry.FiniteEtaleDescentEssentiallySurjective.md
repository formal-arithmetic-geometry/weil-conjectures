## What changed

Withdraw the unused re-export module
Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective through deleted.txt.
Retain its theorem as AlgebraicGeometry.finiteEtaleDescent_essSurj in the existing
upstream module; retain the node's upstream attachment and add a retirement note.
The upstream parent already imports and applies this theorem directly. No Lean
source-library file is changed. Change record:
coord/changes/D9-retire-finite-etale-descent-essentially-surjective.md.

The server compiled the unchanged upstream parent and printed standard-only
axioms for both finiteEtaleDescent_essSurj and finiteEtaleDescent. The wrapper
also compiled. Live and quarantined source searches and the downstream script
found no consumers of the wrapper; the sole DAG parent already uses the upstream
module. The unit route and every mathematical dependency remain available.

## Proved and sorry left

Current item: zero sorry, zero declarations. Closed zero holes; added zero holes;
split off zero. No sorry remains in the delivery. The retirement inventory's
historical one-hole count predates D7's landed replacement. The existing upstream
AlgebraicGeometry.finiteEtaleDescent_essSurj and AlgebraicGeometry.finiteEtaleDescent
are already proved with only propext, Classical.choice and Quot.sound; this
packet claims no new proof credit for them.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective.
Its sole import of WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective
is removed with the wrapper. The upstream module, theorem, DAG node
lem-galois-descent-essentially-surjective, its dependencies and its parent
lem-galois-descent all stay needed and unchanged mathematically. No further
module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The brief and retirement inventory describe a one-hole duplicate, but the live
source has already been reconciled by D7's reviewed delivery, landed as
20261020T135359-L-1817002. The item is now a declaration-free re-export and its
DAG node is attached upstream. This packet completes the requested retirement
against that current source; it neither restores the duplicate nor bypasses the
essential-surjectivity step. There is no quarantine or return entry for this item.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
