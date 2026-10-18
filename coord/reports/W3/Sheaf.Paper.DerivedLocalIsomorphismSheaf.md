## What changed

Proved `AlgebraicGeometry.Scheme.localIsomorphismMap_laws` in
`Sheaf.Paper.DerivedLocalIsomorphismSheaf`, preserving its statement and every existing
construction. Added a proof-only import of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.

The private helpers localize the existing inverse-image identity and associativity
comparisons. The identity law follows by naturality of the derived identity comparison.
For composition, cancel the terminal comparisons, apply naturality of the derived
composition comparison, and use derived associativity at both objects. The proof follows
the existing declaration's documented route, without changing the unit route.
The private helper definitions and local transparency setting are scoped to the proofs.

The complete module compiled on the project server in 12.2 seconds.
`#print axioms AlgebraicGeometry.Scheme.localIsomorphismMap_laws` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.localIsomorphismMap_laws`
(node `def-weil-pbc-derived-local-isomorphism-sheaf`).

No holes remain in the item. No holes were added, and no statements were split off.
The private identity and associativity helpers are fully proved.

## No longer needed

None. No imports, nodes or modules were removed. The existing node has no declared
proof dependencies to prune. The new import supplies the exact-functor localization
coherence used by the proof; no extra sheaf-theoretic obligations are introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The node has no numbered proof steps; the existing
Lean docstring gives the identity/associativity argument that this delivery formalizes.

The static checker requested a change record for the section/local attribute commands:
`coord/changes/derived-local-isomorphism-proof-scope.md`. The attribute is local to
`RestrictionLaws`, and no existing declaration interface or target meaning changes.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
