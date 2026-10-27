## What changed

Proved `CochainComplex.exists_equivariantHomResolutionCalculus` in
`Sheaf.Algebra.Homology.EquivariantHomResolutionCalculus`, preserving its complete statement
and the definition of `productHomResolutionMap`.

Private constructions implement the countable product in each degree, its signed differential,
the bifunctor maps, both signed homotopies, descent to homotopy categories, and the natural
single-source projection isomorphism. The projection API follows the adopted source module
`WeilConjectures.Algebra.Homology.BifunctorHomComplex`, with the differential changed to the
statement's Stacks convention. That source module is unchanged. The only added proof import is
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`, supplying the countability
of the product's index type and the Hom-complex API.

Mathlib's `CochainComplex.IsKInjective.Qh_map_bijective` supplies representatives and detects
homotopies. These give the normalized resolution square, uniqueness, homotopy equivalences for
identified K-injective representatives, and the identity/composition laws. Every step follows
the existing ten-step node plan; no DAG route, statement, or public interface changed.

## Proved and sorry left

Closed one hole: `CochainComplex.exists_equivariantHomResolutionCalculus`
(node `lem-sf-equivariant-hom-resolution-calculus`). Proved 1 of 1 original sorries.
Added zero holes; split off zero statements. No sorry remains in the delivered module.
All private helpers are proved, and all private data definitions are explicit constructions.

## No longer needed

None. No imports removed, no modules withdrawn, and no DAG dependencies pruned. Both
`def-weil-abstract-derived-category` and `lem-weil-pbc-kinjective-hom-derived` remain used.
No unrelated resolution, tensor, or quasi-isomorphism-invariance results are imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The existing source product Hom complex has the
alternative source-degree sign convention, so it cannot be substituted literally for the
requested total-degree differential and homotopy component formulas. The proof retains the
specified formulas, including integer signs in negative degrees, and uses only product
universal properties, additivity, and the cited K-injective bijection.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
