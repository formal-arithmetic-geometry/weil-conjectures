## What changed

Proved `AlgebraicGeometry.Etale.properOpenComparison_comp` by applying injectivity of the
`j₃! ⊣ j₃⁻¹` derived adjunction hom-equivalence to the mate calculation in the new
`Sheaf.AlgebraicGeometry.ProperOpenComparisonCompMate` module, with the canonical
right-derived composition isomorphism. The identity theorem remains an open sorry, and the
canonical direct-image composition isomorphism is unchanged. The new mate module records the
bounded-below injective-representative and fibre-product restriction calculation as its named
remaining theorem.

## Proved and sorry left

Closed the `properOpenComparison_comp` sorry. One original sorry remains in
`AlgebraicGeometry.Etale.properOpenComparison_id`. One new sorry remains, in
`AlgebraicGeometry.Etale.properOpenComparison_comp_mate`, with node
`lem-weil-pbc-proper-open-comparison-composition-mate`.

## No longer needed

The attempted local interchange route and its temporary imports of
`ProperOpenInterchangeComposition`, `ProperOpenInterchangeRefinementNormalization`, and
`ProperSupportSheafComposition` were removed; the final proof uses only the mate module and the
existing comparison definitions. No existing DAG dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The original six-step proof plan leaves the restriction-map calculation implicit. The target
can be reduced cleanly to equality of mates, but that calculation is not available as an existing
Lean declaration; it is therefore split into the new strictly smaller mate statement.

## New nodes

`lem-weil-pbc-proper-open-comparison-composition-mate` states equality after applying the derived
open-immersion adjunction hom-equivalence. Its proof follows the original steps 3–5: compute
restriction on injective representatives, use fibre-product associativity and clopen-section
identification, then use naturality. The node is recorded at
`dag/nodes/sec-smooth-purity/lem-weil-pbc-proper-open-comparison-composition-mate.json`.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
