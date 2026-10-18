## What changed

Proved `AlgebraicGeometry.isClosedImmersion_of_isAffineHom_of_surjective_structureStalks`
in `Sheaf.AlgebraicGeometry.Morphisms.ClosedImmersionOfSurjectiveStructureStalks`,
with its existing signature and docstring unchanged.

Use the canonical `SheafOfModules.unitToPushforwardObjUnit` to view the structure
map as a morphism of modules. The structure modules are quasi-coherent, and
`Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom` makes its target
quasi-coherent. Convert the given ring-stalk surjectivity to local surjectivity.
The local-image and affine-range clauses of `quasiCoherent_cokernel_image` then
produce preimages of sections on every affine open. Conclude with
`isClosedImmersion_iff_isAffineHom`.

The proof uses all five existing proof dependencies and follows the original DAG
route. Added proof-only imports of Mathlib's `PullbackFree` and
`LocallySurjective`. All public imports and all existing signatures are unchanged.
The module compiled through `lcompile.py` in 4.9 seconds without warnings.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.isClosedImmersion_of_isAffineHom_of_surjective_structureStalks`
(node `lem-pc-affine-surjective-structure-map-closed-immersion`).

Holes closed: 1 of 1. Holes added: 0. Sorries left in the delivered module: none.
No split-off statements or additional modules were introduced.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`: it is a retired
re-export of the directly imported source module
`WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.

Replaced the proof-only import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`
with the narrower module
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing`,
which actually declares the quasi-coherence theorem used here. The broader
module's finiteness-of-cohomology result is not used.

No stated proof dependency or unit step is bypassed. No DAG node is pruned;
the two removed module imports are unnecessary for this proof.

## Where the brief, the DAG or earlier work was wrong

The `lean` attachment of `lem-pc-affine-morphism-hi` still names
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`,
but both recorded declarations now reside in its public dependency
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing`.
The imported theorem's actual signature supplies exactly the planned
quasi-coherence assertion, so no statement repair is needed.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
