## What changed

Completed `AlgebraicGeometry.affineGroupoid_coordinate_identities` in
`Sheaf.AlgebraicGeometry.AffineGroupoidCoordinateIdentities`, preserving its signature,
all three tensor constructions and all public imports. The proof supplies the two
possibly different algebra structures on B explicitly to Mathlib's `pullbackSpecIso`,
transports along `Spec.map_preimage`, and retains both projection formulas.
The identity section yields the two counit identities and injectivity; the
composition source/target laws yield the two comultiplication identities.
Equality of the invariant-ring restrictions follows pointwise from membership in
`RingHom.eqLocus`. Updated the node's proof to match the actual calculation.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.affineGroupoid_coordinate_identities`
(node `lem-a1-affine-groupoid-coordinate-identities`).
No holes remain and no holes were added or split off.
Remote single-file compilation passed without errors or warnings in 3.9 seconds.

## No longer needed

Removed the unused proof import `Mathlib.RingTheory.TensorProduct.Maps`.
Removed `lem-weil-pbc-algebra-tensor-pushout-universal-property` from the proof
step uses and proof dependencies: tensor balancing follows instead by faithfulness
of Spec from the pullback square and its projection formulas. That node still
belongs to the statement dependencies for the tensor-ring construction, so this
delivery does not claim its global withdrawal. No Sheaf modules are withdrawn,
and no unit statement or unit proof step is bypassed. No other planned proof
dependency is dropped.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG's proposed direct tensor
balancing argument is valid, but the pullback's own commutative square gives a
shorter formal calculation. Both algebra structures must be passed explicitly:
installing them both as instances on the same type would lose their distinction.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
