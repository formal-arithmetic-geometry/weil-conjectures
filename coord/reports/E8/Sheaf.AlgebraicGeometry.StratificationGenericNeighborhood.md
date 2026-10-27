## What changed

Proved `AlgebraicGeometry.Scheme.exists_stratification_generic_neighborhoods` in
`Sheaf.AlgebraicGeometry.StratificationGenericNeighborhood`, preserving its full signature.
The proof follows all six steps of
`lem-sfb-coefficient-heart-curve-generic-neighborhood` directly from Mathlib and the
existing finite stratification interface:

1. Obtain finitely many irreducible components and their unique generic points.
2. Choose the stratum containing each generic point from the covering partition.
3. Write its locally closed image as an open intersected with a closed set. Remove
   the other finitely many components and intersect with that open to construct W.
4. Use `IsOpenImmersion.range_pullback_to_base_of_left` and injectivity of W's inclusion
   to prove the actual pullback's first projection surjective. Its second projection
   is an open immersion by base change.
5. Base change the stratum immersion. Its surjective image is closed, so
   `IsClosedImmersion.of_isPreimmersion` proves the first projection a closed immersion.
6. Each component lies in the closure of the union because its generic point lies
   in the union. Components cover X, proving density.

The argument uses no reducedness, irreducibility, or dimension assumption. It applies
also to the empty scheme: the pointwise component arguments are vacuous and the density
proof has no points to check. Different components may choose the same stratum. The
actual pullback retains the original stratum scheme structure; no map from W to the
stratum is asserted.

Single-file remote compilation passed after removing the redundant proof imports.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.exists_stratification_generic_neighborhoods`
(node `lem-sfb-coefficient-heart-curve-generic-neighborhood`).

Holes added: 0. Holes left in the delivered module: 0. Split-off statements: 0.
The proof uses only existing proved Mathlib results and the stratification's fields.

## No longer needed

Removed redundant private imports `Mathlib.AlgebraicGeometry.Properties`,
`Mathlib.AlgebraicGeometry.Restrict`, and
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`; the required declarations are already
available through the retained statement imports. All existing public imports remain.

No DAG dependency or project module is pruned: each of the six planned mathematical
steps remains. In particular the open-pullback step uses Mathlib's already proved
range theorem and base-change instance instead of explicitly constructing and swapping
an open-restriction pullback isomorphism. No unit statement or realized proof step is
bypassed, and no upstream declaration is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found in the statement or the DAG plan. The finiteness theorem
`finite_irreducibleComponents_of_isNoetherian` takes its scheme implicitly, so its use
needs an expected type rather than an explicit positional scheme argument.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
