## What changed

Complete the listed retirement of
`Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful` by withdrawing its
unused re-export wrapper through `deleted.txt`. Its upstream theorem remains
proved and unchanged. The current DAG attachment already points to the
upstream theorem, and the mathematical parent imports that upstream module
directly. No node or upstream source is changed.

Change record:
`coord/changes/retire-finite-etale-descent-fully-faithful-wrapper.md`.

Verified the current wrapper through `lcompile.py` (exit 0, 1.4 seconds).
The exact theorem signature is available and its axiom report contains only
`propext`, `Classical.choice`, and `Quot.sound`. `tools/downstream.py`
reports zero wrapper consumers; searches of the Lean tree and quarantine
find none. Read the sole DAG parent `lem-galois-descent`, its complete Lean
proof, and the unchanged `sk-prop-h2` unit route.

## Proved and sorry left

Current item: zero holes before, zero after. Holes closed: none. Holes
added: none. Sorries left in the delivery: none. Split off: none.

`AlgebraicGeometry.finiteEtaleDescent_fullyFaithful`
(node `lem-galois-descent-fully-faithful`) is already completely proved in
`WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful`; its
standard-axiom report was verified in this session. This delivery claims
retirement progress only, not a newly proved theorem.

## No longer needed

Withdraw the module
`Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful`, including its
redundant public re-export import of
`WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful`.

No mathematical dependency is pruned: retain
`lem-galois-descent-fully-faithful`, its upstream module, and all of its
statement/proof dependencies. Its parent needs the theorem and already uses
its upstream proof. There are no consumer imports to adapt, including in
quarantined modules. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retirement inventory says one sorry and describes the old lowercase
compatibility predicate. D7's reviewed landing
`20261020T135359-L-1817002` already removed that duplicate, replaced this
module by an upstream re-export, and repointed its node. The live source
therefore has zero holes. The remaining concrete retirement is removal of
the now-unused wrapper. The node and its mathematical parent's proof are
current and retained, rather than withdrawn on the basis of zero importers.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
