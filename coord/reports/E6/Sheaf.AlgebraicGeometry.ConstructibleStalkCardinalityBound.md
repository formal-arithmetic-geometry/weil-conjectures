## What changed

Completed the depth-zero retirement item from `coord/retire-items.tsv`.
Withdrew `Sheaf.AlgebraicGeometry.ConstructibleStalkCardinalityBound` in favour of
`WeilConjectures.AlgebraicGeometry.ConstructibleStalkCardinalityBound`.
Changed the sole direct consumer,
`Sheaf.AlgebraicGeometry.ConstructibleCurveAnnihilator`, by replacing that one
proof-only import. Its existing proof applies the identical upstream theorem
without modification. No upstream files or target statements were changed.

Reattached node `lem-weil-pbc-constructible-stalk-cardinality-bound` to the existing
upstream declaration `AlgebraicGeometry.Scheme.exists_stalk_cardinality_bound_of_constructible`.
Updated its proof description to mention the upstream separably closed stalk API.
Its statement, dependencies, and the unit route remain unchanged. Change record:
`coord/changes/retire-constructible-stalk-cardinality-bound.md`.

## Proved and sorry left

This is a duplicate retirement with zero original holes, zero holes closed,
zero holes added, and zero holes remaining in the delivered consumer or retired
item. Nothing was split off. The cardinality bound was already completely proved
in both modules. Its upstream implementation's `#print axioms` returned exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The original item compiled in 3.1 seconds. The consumer after import substitution
compiled without warnings in 2.0 seconds; its proof body and all public signatures
are unchanged. The upstream theorem signature and both modules' complete import
lists were compared verbatim and agree. The upstream private helper generalization
requires no consumer adaptation. Empty schemes and zero sheaves remain covered by
the same unchanged public statement and compact finite-cover argument.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.ConstructibleStalkCardinalityBound` and removed its
proof-only import from `Sheaf.AlgebraicGeometry.ConstructibleCurveAnnihilator`.
The upstream module supplies the replacement. No mathematical node or dependency
is pruned: the sole DAG parent retains the cardinality-bound node, whose Lean
attachment now points upstream. The source library and every upstream declaration
remain intact. All five indirect consumers keep their existing public environment.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a repeatedly split proof obligation, but the
current item already has no sorry. Its current assignment is the explicit
retirement row, whose only API differences concern private helper lemmas.
The pending-consumer reason in the older kept-twins table is obsolete: the direct
consumer is now unclaimed, its one import replacement compiles, and no public
signature adaptation is needed.

Searches run: LeanFinder for uniformly bounded geometric stalk cardinalities
(eight unrelated Mathlib results), Loogle for `Nat.card_congr` (exact lemma found),
and Mathlib grep for `stalk.*card|card.*stalk` (no hits). Direct project searches
found the already proved upstream theorem with the identical public signature.
`tools/downstream.py` found one direct and five indirect consumers; only the direct
consumer mentions the theorem. No new nodes or new mathematical claims were needed.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
