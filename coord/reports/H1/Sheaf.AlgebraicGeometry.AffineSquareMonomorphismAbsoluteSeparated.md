## What changed

Filled the proof of `AlgebraicGeometry.affine_square_monomorphism_absolute_separated`
in `Sheaf.AlgebraicGeometry.AffineSquareMonomorphismAbsoluteSeparated`.
The statement, canonical comparison definition, public imports and docstrings are unchanged.

The proof follows all four DAG steps. It transports the absolute square along the given
isomorphism and the terminal isomorphism to `Spec (ULift ℤ)`, applies `pullbackSpecIso`,
and uses `Algebra.TensorProduct.equivOfCompatibleSMul` to identify the lifted-integer
and integer tensor products. Explicit ring-map equations prove both projection identities.
Pullback uniqueness proves comparison monicity. Composition gives monicity of the map
from R; Mathlib supplies its separatedness. Affineness of the absolute square and
composition of separated morphisms give absolute separatedness of R.

The LeanFinder, Loogle and grep searches through `msearch.py`, together with direct
searches of Mathlib and both library roots, found these component lemmas and no
existing theorem for the complete statement. No additional imports are needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affine_square_monomorphism_absolute_separated`
(node `lem-trf-affine-square-monomorphism-absolute-separated`).
One of one holes proved; zero holes added; zero holes remain; zero split off.

## No longer needed

None. All four declared proof dependencies are used, through their Mathlib declarations.
No imports, nodes or modules are removed. The existing unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The proof plan suppresses the universe bookkeeping:
`pullbackSpecIso` needs its three rings in the same universe, so the proof uses
`ULift ℤ` and the canonical tensor-product equivalence before obtaining the stated
tensor product over ℤ. This does not change any statement or definition.
The compatibility hypothesis `hj` is not needed by the proof; it is preserved verbatim.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
