## What changed

Proved `CategoryTheory.Functor.finiteColimit_matrix_cokernels` in
`Sheaf.CategoryTheory.FiniteColimitMatrixCokernels`, with its statement and the existing
`finiteColimitBiproductIso` construction unchanged. The proof obtains additivity from
`rightExactFunctor_le_additiveFunctor`, checks the coproduct comparison on injections,
checks projections and the matrix square by biproduct extensionality, and transports the
preserved cokernel cofork along the resulting arrow isomorphism. Cofork extensionality
proves uniqueness from the forward projection equation.

Validation: the complete module compiled through `lcompile.py` in 3.2 seconds,
with no errors or warnings.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.finiteColimit_matrix_cokernels`
(node `lem-sfb-finite-colimit-matrix-cokernels`). No holes added; no `sorry` remains.
No statements were split off.

## No longer needed

None. The existing DAG dependencies and eight-step argument are retained; Mathlib's
biproduct and cofork APIs implement their universal-property calculations. No project
module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. Empty finite index types are handled by the same extensionality arguments, with
no nonemptiness assumption. The proof uses only finite coproduct and cokernel
preservation, as required, and applies to arbitrary colimiting cokernel coforks.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
