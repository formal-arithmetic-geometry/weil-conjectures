## What changed

Restored `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat` from the
quarantine recorded in `coord/rework.tsv`, as a public compatibility import of
`WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat`. The adopted
source already completely proves
`AlgebraicGeometry.derivedPullback_tensor_unit_kFlat`. Reusing it repairs the
conflicting derived-pullback import and avoids a second declaration of the same
public theorem. No adopted source module was edited.

The node `lem-pc-derived-pullback-tensor-unit-kflat-coherence` retains its
statement, dependencies and complete proof plan. Its Lean attachment now names
the existing adopted source theorem and copies that theorem's exact signature.
The canonical source names the K-flat predicate `IsKFlatTensor`; its defining
acyclic-tensor condition is the former `IsAcyclicTensorKFlat` condition. All
binders, universes, conclusions and the explicit unit comparison agree.

Read the source proof against the recorded three-step plan and Stacks
`cohomology.tex`, `lemma-pullback-tensor-product` (Tag 079U). It proves K-flat
counit invertibility by left-derived uniqueness, computes both complex unit laws
on the degree-zero summand, and applies the normalization and cancellable lax
squares to obtain both derived unit laws. There is no new proof route or unit
bypass. The right-unitor proof of unit K-flatness also works on zero complexes
and empty schemes; no boundedness condition is introduced.

The original quarantined file reproduced the recorded duplicate-import error
in 0.8 seconds. The restored module compiled through `lcompile.py` in 1.5 seconds.
A separate consumer probe compiled in 10.3 seconds: it reconstructs the old
acyclic-tensor predicate on schemes, proves its equivalence to `IsKFlatTensor`
by `Iff.rfl`, and applies the source theorem to the entire old theorem signature
unchanged apart from the local name of that predicate. This checks all supplied
comparison maps, both unit conclusions, all binders and the caller argument order.
The probe was kept under `scratchpad/`, outside the delivery's Lean module set.
The axiom probe reports only `propext`, `Classical.choice` and `Quot.sound` for
the reused theorem.

Change record: `coord/changes/Q1-derived-pullback-tensor-unit-kflat-rework.md`.

## Proved and sorry left

This is a zero-hole sync repair. The quarantined item contained zero `sorry`s;
the restored module contains zero. The reused theorem
`AlgebraicGeometry.derivedPullback_tensor_unit_kFlat` and all private helpers in
its adopted source module have complete proofs. Holes closed: none (0 of 0).
Holes added: none. Split off: none. No remaining holed declaration is introduced
or hidden by this packet.

## No longer needed

The duplicate local implementation and its private helper proofs are replaced
by the adopted implementation. Removed direct imports from the Sheaf file:
`Sheaf.AlgebraicGeometry.DerivedPullback`,
`WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`,
`WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare`, and
`WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitNormalization`.
The former direct public import
`WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnitCounit` is supplied
publicly through the adopted K-flat unit module. Its proof dependencies are
still used by the source proof, so no mathematical node is pruned. No module is
withdrawn and no archive is deleted.

## Where the brief, the DAG or earlier work was wrong

The generic prove-a-sorry brief does not describe this item's current state:
it is quarantined, already fully proved rework. The earlier Sheaf implementation
imports a second `AlgebraicGeometry.derivedPullback` after the canonical adopted
one is already present, causing its assigned compilation error. The upstream
counterpart is a complete replacement, with only the K-flat predicate renamed
in its public signature. The Lean attachment previously pointed at the
quarantined duplicate and is reconciled with that counterpart.

A source scan of both `lean/` and `quarantine/` found the only direct Sheaf-path
consumer, quarantined `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit`, and
the existing canonical consumer
`WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnit`. Both use the same
public theorem name and its left/right conjuncts. The sole DAG parent is
`lem-pc-derived-pullback-tensor-unit`; it and its dependency are preserved.
`tools/downstream.py` reports the assigned missing live module as unknown, so
the scan explicitly included its quarantine archive. No consumer adaptation is
forced; the quarantined parent's independent sync defects remain its own repair.

The required Mathlib searches were run with `msearch.py`: the unit-law LeanFinder
query returned Tor and flat-module exactness ingredients, with no exact theorem;
the Loogle name query did not resolve the queried unitality name; the grep query
returned no hits. A direct source search and comparison found the complete exact
adopted counterpart and its predicate-name difference. This existing result is
the shortest route and requires no new nodes.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
