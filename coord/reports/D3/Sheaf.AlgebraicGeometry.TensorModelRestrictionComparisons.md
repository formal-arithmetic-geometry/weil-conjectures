## What changed

Restored the quarantined module and kept its existing complete proof of
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_comparisons`. Updated
only its imports so it compiles after the 2026-10-20 upstream synchronization:
`Sheaf.AlgebraicGeometry.DerivedTensorAugmentation` was removed because the
source canonical tensor-Hom import already provides the corresponding source
notion, and `Sheaf.Algebra.Homology.KFlat` was made a public import because the
statement exposes `CochainComplex.IsAcyclicTensorKFlat`.

The private categorical transport lemma and the public theorem are unchanged.
The module compiles on its own and with all sandbox files.

## Proved and sorry left

The existing proof of
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_comparisons` remains
complete. It has no remaining `sorry`; no new `sorry` was added.

## No longer needed

The public import of `Sheaf.AlgebraicGeometry.DerivedTensorAugmentation` is no
longer needed: it conflicts with the source declaration imported by
`WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom`. No proof
dependency or DAG node was pruned.

## Where the brief, the DAG or earlier work was wrong

The quarantined copy retained a public Sheaf import of
`DerivedTensorAugmentation` while also importing the upstream canonical
DerivedTensorHom module. The two imports define the same declaration in one
environment, producing the reported duplicate-environment error. The source
canonical import is sufficient for the proof; the explicit public KFlat import
is required to expose the Sheaf K-flat predicate in the theorem statement.
The theorem statement and proof route remain unchanged. The import adaptation is recorded in `coord/changes/tensor-model-restriction-comparisons-rework-20261020.md`.

## New nodes

None.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
