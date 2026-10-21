## What changed

Proved `AlgebraicGeometry.ProEtale.scalarMatrix_inverseImage` using naturality of
`upperStarFromPointComp` for the scalar endomorphism, the existing
`Mod.regularExtensionIso_naturality`, finite biproduct universal properties, and
`PreservesCokernel.iso`. All four helper lemmas are private and proved. Both canonical
comparison definitions and all public signatures and public imports are unchanged.
The proof follows the six steps already recorded in the current DAG; no node is added.
The unit's local-coefficient-model route is preserved.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProEtale.scalarMatrix_inverseImage`, node
`lem-sfb-scalar-matrix-inverse-image`. Added zero holes, split off zero statements.
No sorry remains in the delivered module; no other Lean module is changed.
The complete module compiled remotely in 10.7 seconds. Its axiom check lists only
`propext`, `Classical.choice`, and `Quot.sound`. Fixed the two line-length warnings
before the final delivery compile. Verified all public signatures, imports, and
both comparison definition bodies against the shared source, unchanged.

## No longer needed

Removed redundant private imports `Sheaf.CategoryTheory.SheafTensor`,
`Mathlib.CategoryTheory.Monoidal.Bimod`, and `Mathlib.CategoryTheory.Adjunction.Limits`.
The existing regular-extension comparison and pullback instances supply their roles.
Added the proof import `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`.
The current DAG already records the regular-extension API rather than separate
mixed-bimodule-unitor and adjoint-colimit proof dependencies, so no further proof
edge is removed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction is needed. The earlier F3 report describes the same useful
route, but the current module contains the original hole. Reconstructed the proof
against the current sources. The cokernel projection identity is discharged with
`cokernel.π_desc`; the current API has no `cokernel.π_map` lemma. Scoped elaboration
options permit conversion of transported module types without changing definitions.
The change record is `coord/changes/S8-scalar-matrix-proof-elaboration.md`.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
