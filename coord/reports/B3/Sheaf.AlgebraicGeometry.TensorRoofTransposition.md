## What changed

Restored `Sheaf.AlgebraicGeometry.TensorRoofTransposition` from its rework archive.
Replaced the retired, empty public import
`Sheaf.AlgebraicGeometry.DerivedTensorAugmentation` with direct public imports of
`Sheaf.Algebra.Homology.KFlat` and
`WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`.
The existing public internal-Hom import and private proof-dependency import stay.
Every declaration, proof, docstring, attribute and option is unchanged.
Change record: `coord/changes/tensor-roof-transposition-rework-20261020.md`.

The restored module compiles remotely. A dedicated public-import consumer checks
`Scheme`, `schemeDerivedCategory`, `IsAcyclicTensorKFlat`, `tensorUnit`,
`derivedInternalHom` and `tensor_roof_transposition`; both files compile cleanly.
`#print axioms tensor_roof_transposition` reports only `propext`,
`Classical.choice` and `Quot.sound`.
The proof follows the existing node: transpose using the simultaneous adjunction;
prove invertibility using surjectivity and injectivity of precomposition; cancel
the restricted unit isomorphism and use naturality for the required identity.
This categorical argument includes the empty open and zero model.

## Proved and sorry left

This is a zero-hole quarantine repair, not a new hole closure.
`AlgebraicGeometry.Scheme.tensor_roof_transposition`
(node `lem-sc-tensor-roof-transposition`) has its complete existing proof restored.
Holes closed: 0 of 0. Holes added: 0. Split off: 0. Sorries left: none.

## No longer needed

Removed the unused import `Sheaf.AlgebraicGeometry.DerivedTensorAugmentation`;
that withdrawn empty module provides no declarations. No DAG node, proof
dependency, unit step or other module is withdrawn. In particular,
`lem-sc-tensor-model-restriction-adjunction` remains the proof dependency and its
module remains privately imported.

The local source search finds the upstream theorem with the same name, but the
adopted source uses a separate dependency tree. Importing that theorem would
introduce conflicting declarations; the retained Sheaf proof is already complete.
Mathlib searches for the tensor-Hom augmentation argument found no shorter exact
replacement; Loogle confirms the existing `Iso.homCongr` transport API.

## Where the brief, the DAG or earlier work was wrong

The archived file already has zero sorries: its assignment is the listed import
repair after upstream synchronization. The old augmentation import became empty,
so it no longer publicly supplies the definitions used in the theorem statement.
The current node's statement, Lean attachment and proof route need no changes.

The only source consumer is quarantined `AffinePerfectTensorRoof`. A scratch
compile fails at its existing duplicate `IsPerfect` import, before applying this
theorem. Its independent import collision is not caused by this repair and no
consumer signature or proof adaptation is necessary here.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
