## What changed

Proved `AlgebraicGeometry.product_tangentSpace_directSum` by the existing DAG route:
the projection differentials give a linear map to the product; the sum of the two
inclusion differentials gives its inverse. The four projection/inclusion composites
are the identity and zero maps. Equality of maps into the scheme pullback proves
injectivity. The inverse formulas on the two summands follow from linearity.

Added proved private helpers for naturality of the structural residue-field map,
rationality of images, restriction of a differential to base-field scalars,
composition of dual-number coefficient identifications, and constant tangent maps.
The public theorem statement and public imports are unchanged.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.product_tangentSpace_directSum`
(node `lem-sc-product-tangent-space-direct-sum`). No holes added or split off.
No `sorry` remains in the delivered module.

## No longer needed

None. All four declared proof dependencies are used. The existing proof imports
`WeilConjectures.AlgebraicGeometry.TangentMapLinear` and
`WeilConjectures.AlgebraicGeometry.TangentVectorsVectorSpace` supply the linearity
and specified zero-vector formula. No nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The Lean proof makes explicit the residue-field
identifications implicit in the DAG: the image of a rational point under `(1,y)` is
rational; the two sections define the same product point; and the residue-field
linear maps restrict to the base field through the structural ring maps.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
