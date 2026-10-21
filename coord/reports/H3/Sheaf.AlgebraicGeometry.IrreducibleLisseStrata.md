## What changed

Retired the zero-hole duplicate module
`Sheaf.AlgebraicGeometry.IrreducibleLisseStrata` via `deleted.txt` and rebound
`lem-weil-pbc-irreducible-lisse-strata` to
`WeilConjectures.AlgebraicGeometry.IrreducibleLisseStrata` and its existing theorem
`AlgebraicGeometry.Scheme.exists_irreducible_lisse_stratification`.

The upstream theorem proves the identical statement: `IsLisseEtaleSheafOfSets`
is definitionally `IsFiniteLocallyConstantSheafOfTypes`. A scratch Lean probe
applied the upstream theorem at the original signature unchanged and compiled
in 2.1 seconds. Its axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
No source-library code, target statement, definition, or proof route changed.

## Proved and sorry left

Initial holes: zero. Holes closed: zero. Holes added: zero. Split off: zero.
There are no remaining sorries in this delivery. The retained theorem
`AlgebraicGeometry.Scheme.exists_irreducible_lisse_stratification` is completely
proved. This delivery claims duplicate retirement, not new proof progress.

## No longer needed

The duplicate module `Sheaf.AlgebraicGeometry.IrreducibleLisseStrata`, its duplicate
declaration, and its imports of `WeilConjectures.AlgebraicGeometry.EtaleSheaves`,
`Mathlib.AlgebraicGeometry.Noetherian`, and
`WeilConjectures.AlgebraicGeometry.IrreducibleLisseRefinement` are no longer needed
in that duplicate module. These mathematical dependencies remain in the adopted
provider. No mathematical node, dependency, or unit step is pruned.

No current module imports the duplicate, including quarantined sources. Its
historical Sheaf consumer has already been retired. The sole actual DAG parent,
`lem-weil-pbc-constructible-finite-stalk-tests`, is attached to
`WeilConjectures.AlgebraicGeometry.ConstructibleFiniteStalkTests`, which already
imports and uses the adopted provider. All parents were checked, so zero current
importers is not the sole basis for retirement. The node stays attached to its
proved adopted replacement and remains available to unfinished parent proofs.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module containing a sorry, but the specific
row in `coord/retire-items.tsv` requests retirement of an already proved duplicate.
Its node still named the Sheaf duplicate and recorded an obsolete finite-local-
constancy predicate spelling. The replacement attachment records the retained
source signature verbatim. The mathematical statement is unchanged.

Change record: `coord/changes/irreducible-lisse-strata-retire-H3.md`.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
