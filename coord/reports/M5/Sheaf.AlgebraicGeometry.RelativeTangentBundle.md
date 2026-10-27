## What changed

Proved both theorems in Sheaf.AlgebraicGeometry.RelativeTangentBundle without changing any
statement or definition. The section identity is the over-category equation. The affine chart
proof combines the affine section comparison, the counit on sections, scalar compatibility,
and the augmentation identity. Removed the unused CoherentFiniteType import and two
redundant imports already supplied by VectorBundleZeroSection. Two proved private helpers record
the full-faithful preimage and its pullback equation. The proof adapts the existing VectorBundleZeroSection argument
without requiring a Noetherian base or constant relative dimension. Updated the defining
node pur9-dg-def-tangent with the argument and dependencies actually used.
Change record: coord/changes/relative-tangent-bundle-import-pruning.md.

## Proved and sorry left

Closed 2 of 2 holes:

- AlgebraicGeometry.RelativeTangentBundle.zeroSection_comp_projection.
- AlgebraicGeometry.RelativeTangentBundle.affineChart_spec.

Added no holes and split off no statements. No sorry remains in the delivered module.
The imported relativeDifferentials_isQuasicoherent remains an existing dependency;
its proof is outside this item.

## No longer needed

Removed the unused public import Sheaf.AlgebraicGeometry.CoherentFiniteType (node
pqf-def-coherent). Removed redundant public imports
Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore and
WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec: both remain publicly
available through VectorBundleZeroSection, which supplies the concrete general API.
These two construction nodes remain needed transitively and are not pruned from the DAG.
No modules or nodes withdrawn. The constant-rank and Noetherian
vector-bundle wrappers and their trivialization and transition results are not used;
only the existing general anti-equivalence, augmentation, and augmentation_spec API
are needed from VectorBundleZeroSection. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The definition node previously had an empty proof and proof_deps despite its two
comparison theorems. The node now records their proofs. No statement correction was
needed. Empty schemes and affine opens, varying relative dimension, and relative
dimension zero require no separate case: the proof uses the affine and over-category
APIs directly.

The first preflight required the import-pruning change record; it is now included.
The two consumers were quarantined during the shared refresh, and their preserved
source archives were checked without modification.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
