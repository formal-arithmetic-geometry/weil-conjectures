## What changed

Proved `CochainComplex.exists_finite_matrix_model_of_projective_over_dvr` in
`Sheaf.Algebra.Homology.DVRProjectiveComplexMatrixModel`, with its signature unchanged.
The section of the canonical free-module surjection supplied by `Module.Projective.out`
is injective, so torsion-freeness pulls back from the free module. Mathlib's existing
PID finite-torsion-free instance gives freeness. Set the rank in each degree to
`Module.finrank` and use `Module.finBasis.equivFun.symm` as the coordinate equivalence.
`ModuleCat.subsingleton_of_isZero` and zero finrank give precisely the required support.
The differentials are `LinearMap.toMatrix` in those bases. The matrix/vector
compatibility and zero matrix products follow from `toMatrix_mulVec_repr`,
`toMatrix_comp`, and the original complex's `d_comp_d`.

Added the proof-only import `Mathlib.LinearAlgebra.Dimension.Free` for finite bases.
The existing DAG plan is followed, with Mathlib's coordinate API performing its
finite-sum and matrix-entry calculations. No statement, definition, public import,
consumer, or DAG route changes.

Validation: the complete module compiles through `lcompile.py` without warnings
(4.3 seconds of server compilation).

## Proved and sorry left

Closed 1 hole:
`CochainComplex.exists_finite_matrix_model_of_projective_over_dvr`
(node `lem-sfb-dvr-projective-complex-matrix-model`).
Added 0 holes; 0 holes remain in the delivered module. No decomposition or new lemma.

## No longer needed

Removed the redundant proof-only import `Mathlib.LinearAlgebra.FreeModule.Basic`:
the retained `Mathlib.LinearAlgebra.FreeModule.PID` already imports it.
No mathematical dependencies, nodes, or modules are pruned. All stated proof
dependencies are existing Mathlib leaves and remain used in the original route.

## Where the brief, the DAG or earlier work was wrong

None. The proof also covers zero terms, empty matrices, a one-degree interval, and
negative degrees, with independent universes for the ring and module carriers.
The interval-order hypothesis is retained verbatim; the construction works without
using it, since support is inherited degree by degree.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
