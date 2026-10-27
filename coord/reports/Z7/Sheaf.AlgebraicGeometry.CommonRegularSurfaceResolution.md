## What changed

Proved `AlgebraicGeometry.exists_common_regular_surface_resolution` in
`Sheaf.AlgebraicGeometry.CommonRegularSurfaceResolution`, preserving its statement,
public imports, and the four-step DAG route of Stacks Project Tag 0C5S
(`resolve.tex`, `lemma-birational-regular-surfaces`). Added private proof imports of
`Sheaf.AlgebraicGeometry.SurfaceRationalMapPointResolution` and
`Sheaf.AlgebraicGeometry.ProperBirationalSurfaceFactorization`.

Mathlib's locally-finite-type Noetherianity and quasi-compactness lemmas give
Noetherianity of both surfaces. Elimination of indeterminacy supplies the first
tower, its regular integral Noetherian surface top, and the extension `g`.
The base compatibility identity and proper composition make `g` proper by
`IsProper.of_comp`. The inverse of the restriction isomorphism sends a point of
the original nonempty dense open into its inverse image; this inverse image is
therefore a dense open of the integral top. Composing the restriction isomorphism
with the specified `α` gives exactly the birationality witness required by the
factorization theorem. That theorem supplies the second tower. Both maps to the
base, reduced closed point centers, and the final restriction identity are then
assembled directly from these witnesses.

The original proof dependencies are all used, so no node update is necessary.
The zero-length case is covered uniformly: the first tower is identified with
its own top by `Iso.refl`, and no nonempty index set is assumed for either tower.
The theorem's hypotheses imply both dense opens are nonempty by integrality;
there is no extra nonemptiness hypothesis.

The shorter-route search used launcher LeanFinder and Loogle, and searches of
Mathlib and both library roots. The rational-map search hits do not supply common
point-blowup resolution; the stated two inputs already give the direct source
proof. Both proof imports passed the import-direction check. The final module
compiled through `lcompile.py` with exit code 0 in 6.7 seconds and no warnings.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_common_regular_surface_resolution`
(node `lem-sfb-common-regular-surface-resolution`).

There are no remaining `sorry`s in the item, no added holes, and no split-off
statements. The existing imported theorems
`AlgebraicGeometry.exists_surface_rational_map_point_resolution` and
`AlgebraicGeometry.exists_point_blowup_factorization_of_proper_birational`
remain separate project inputs; their proofs are not changed in this delivery.

## No longer needed

None. No imports, modules, or declared proof dependencies were pruned. The proof
uses every dependency of the existing four-step plan and introduces no new node.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The two declared surface theorems fit
the intended argument without adaptation. No definitions or statements changed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
