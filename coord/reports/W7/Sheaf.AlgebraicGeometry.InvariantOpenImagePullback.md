## What changed

Proved `AlgebraicGeometry.invariant_open_image_pullback` in
`Sheaf.AlgebraicGeometry.InvariantOpenImagePullback`, preserving its signature and all imports.
The proof follows the existing six-step DAG plan. The scheme pullback image formula and
invariance give saturation. The fpqc quotient-map theorem gives openness; surjectivity gives
uniqueness among all subsets. Open-immersion lifting constructs the morphism, and Mathlib's
open-immersion pullback criterion proves the cartesian square. Pasting with the square
presented by `theta` constructs the final pullback isomorphism with both projection equations.
Cancelling the monic open inclusion proves compatibility with the actual given transport.

The source read was Stacks Project `descent.tex`, Tag 0247, `lemma-quasi-affine`, final
paragraph. The existing DAG dependencies supply the Mathlib APIs used, including the
pullback and open-immersion universal properties. No statements or definitions changed.
The file compiled without warnings through `lcompile.py` (5.3 seconds).

## Proved and sorry left

Closed one of one existing holes:
`AlgebraicGeometry.invariant_open_image_pullback`
(node `lem-trf-invariant-open-image-pullback`).
No holes remain in the item, no holes were added, and no lemmas were split off.

## No longer needed

None. No imports, modules, or DAG dependencies were removed. Every original proof dependency
remains used: the scheme image formula, open immersion and its lifting and monomorphism
properties, the quotient-map theorem, fibre products, and descent data.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The proof uses the existing Mathlib open-immersion pullback
criterion and pullback pasting to implement the universal-property arguments in steps 4
and 5. In particular, it never identifies scheme fibre-product points with pairs of points.
The empty open and the whole open require no extra assumptions or separate cases.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
