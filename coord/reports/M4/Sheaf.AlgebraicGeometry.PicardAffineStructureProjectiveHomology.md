## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PicardAffineStructureProjectiveHomology.lean`
from the quarantine path recorded in `coord/rework.tsv`. The archived public imports,
theorem signature, complete proof, and blueprint attachment are preserved.

The proof obtains K-flatness from the supplied bounded projective complex and applies
`picard_affine_projective_base_change`. Exact affine sheafification identifies the
homology of the scalar-extended complex with sections of the corresponding higher
direct image. Connectivity of a right derived functor gives negative vanishing;
its degree-zero comparison, the supplied adjunction-unit isomorphism, and the tensor
pullback structure-sheaf isomorphism identify zeroth homology with the new ring.

The complete restored module compiles cleanly through `lcompile.py` in 19.0 seconds
against the published green build. Library and Mathlib searches confirmed that the
existing affine comparison and right-derived homology API give the required route;
no new intermediate statement is necessary.

## Proved and sorry left

This is restoration of a quarantined, already proved module. The archive has zero
holes, and the restored module has zero holes. No holes are closed or added, and no
statements are split off. The theorem
`AlgebraicGeometry.Scheme.picard_affine_structure_projective_homology` has a complete
proof, with no new axioms or definitions.

## No longer needed

None. Every recorded proof dependency is retained: bounded-flat K-flatness, affine
projective base change, exact tilde homology, and tensor pullback of the structure
sheaf. No module or DAG node is withdrawn, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The assigned source was absent from `lean/` because it was quarantined after the
cluster restore, rather than withdrawn. Its exact preserved source is the rework
row's quarantine archive. The assignment is therefore a zero-hole restoration,
rather than another decomposition of the homology argument.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
