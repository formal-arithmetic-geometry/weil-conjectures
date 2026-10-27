## What changed

Proved `AlgebraicGeometry.infinite_closedPoints_inter_of_topologicalKrullDim_pos`
in its assigned module, with exactly its existing signature and public imports.
Updated its proof docstring and DAG proof to the shorter Jacobson-space argument.
The proof uses only Mathlib: local finite type over a field makes X Jacobson;
the closed subspace Z is Jacobson, and finiteness of its ambient closed points
would make Z discrete and hence of dimension at most zero.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.infinite_closedPoints_inter_of_topologicalKrullDim_pos`
(node `lem-sc-positive-dimensional-locally-algebraic-closed-points`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivery.
The server compile succeeded (1.4 seconds); `#print axioms` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. A declaration-scoped linter
option suppresses the intentionally unused, preserved irreducibility binder;
no proof-checking option is changed.

## No longer needed

Removed all four proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ClosedPointOfAffineOpen`, node
  `lem-sc-affine-maximal-points-closed-in-lft-scheme`: no affine opens are used.
- `WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic`, node
  `lem-sc-dimension-locally-algebraic`: no comparison with an affine open's
  dimension is needed.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`, node
  `lem-weil-pbc-reduced-induced-closed-subscheme`: the argument uses only the
  closed topological subspace Z, not an induced scheme structure.
- `Sheaf.RingTheory.InfiniteSetOfIsMaximalOfRingKrullDimPos`, node
  `lem-sc-fg-domain-positive-dimension-infinite-maximals`: no coordinate ring
  or maximal ideals are needed.

Also removed these unused original proof-dependency entries:
`def-weil-finite-type-morphism`, `def-weil-irreducible-components`,
`def-weil-affine-spectrum`, `def-weil-closed-immersion`,
`def-weil-pbc-finite-type-algebra`, and `def-weil-pbc-krull-dimension-ring`.
The first two remain statement dependencies. Removed obsolete `tool_uses`
approvals for `lem-sc-dimension-locally-algebraic` (both duplicate entries)
and `lem-weil-pbc-reduced-induced-closed-subscheme`.
These dependencies are pruned from this proof only; no module or declaration
is withdrawn, and the source-library modules are untouched.

## Where the brief, the DAG or earlier work was wrong

The planned affine reduction was unnecessary. Mathlib already provides
`LocallyOfFiniteType.jacobsonSpace`, `JacobsonSpace.of_isClosedEmbedding`,
`IsClosedEmbedding.preimage_closedPoints`, `JacobsonSpace.discreteTopology`,
and `topologicalKrullDim_zero_of_discreteTopology`. Searches via LeanFinder,
Loogle, the prescribed grep service, and local source inspection established
this route. The proof even works without irreducibility; the original
hypothesis and signature are preserved. Empty or zero-dimensional Z cannot
satisfy the positive-dimension hypothesis; the argument also applies when
the dimension is infinite. No unit statement or unit proof step is bypassed:
the item is below the unit route, and is not a realized unit node.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
