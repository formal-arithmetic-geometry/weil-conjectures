## What changed

Proved `CategoryTheory.ordinaryTriangleCounitCone` in
`Sheaf.CategoryTheory.OrdinaryTriangleCounitCone`, preserving its statement, all six universe
parameters and all hypotheses. The proof adds the proof-only import
`WeilConjectures.CategoryTheory.Triangulated.Recollement` and reuses its already proved
`exists_distTriang_counit_unit` and `subsingleton_hom_shift` declarations. The ordinary
triangle shows directly that every object killed by `jStar` is in the essential image of
`iStar`; the invertible closed counit gives full faithfulness. Comparing the source
recollement triangle with the given completion by `isoTriangleOfIso₁₂` supplies the required
isomorphism. Shifted orthogonality and Hom-out exactness prove uniqueness.

Converted the legacy non-module header to the required `module`/`public import`/
`@[expose] public section` layout. Both existing Mathlib imports serve the public statement
and remain public. No existing declaration or definition was changed. Updated the theorem's
proof documentation and the node's proof, proof_deps and proof_origin to record this route.
The unit `sk-prop-sf-localization` has no realized statement or proof-step nodes; this changes
only the auxiliary node route and retains the ordinary-triangle input.

Documented the required module-header conversion in
`coord/changes/ordinaryTriangleCounitConeModule.md`. The theorem signature is byte-identical
to the original, and a source search finds no external importer or user to adapt.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.ordinaryTriangleCounitCone`
(node `lem-sf-ordinary-triangle-counit-cone`). One of one holes proved; zero holes added,
zero split off, zero remaining in the delivered module. The library recollement declarations
used here have complete proofs. No new declarations, axioms or definitions were added.

## No longer needed

The direct Yoneda Hom-set detection step and its node
`lem-coef-joyal-homset-iso-detection` are unnecessary: the third component of an isomorphism of
distinguished triangles is already an isomorphism. Removed this node from proof_deps.
The long direct closed-orthogonality and Hom-comparison argument is replaced by the existing
source-library recollement construction. Hom-into and Hom-out exactness remain dependencies
of that construction and triangle comparison; the fully faithful adjunction node remains used.
No original imports were removed, no module was withdrawn, and no other planned dependency
node is pruned. A trial explicit import of `Mathlib.CategoryTheory.Adjunction.FullyFaithful`
was removed because the source recollement import already supplies it.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's direct six-step proof is valid but unnecessary because
the source library already proves the formal recollement triangle. Its essential-image
hypothesis follows from the supplied ordinary triangle with zero first vertex. The legacy
file lacked the module-system header required by the current brief; this delivery corrects
that layout. The proof needs only pretriangulated categories, but the three original
`IsTriangulated` hypotheses are explicitly retained, so no signature is weakened.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
