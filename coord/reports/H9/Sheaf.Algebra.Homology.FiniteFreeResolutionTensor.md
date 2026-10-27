## What changed

Completed `SheafOfModules.FiniteFreeResolution.finiteFreeResolution_tensor` in
`Sheaf.Algebra.Homology.FiniteFreeResolutionTensor`. It constructs the finite-power
complex with its conjugated differential, the normalized derived comparison from
the specified augmentation, the tensor summand equations, the sectionwise matrix
formula, and the two support specializations. Private proved helpers handle scalar
actions through tensor sheafification and the finite-coordinate calculation. A
private generic cochain transport construction avoids unfolding concrete tensor data.
Existing public signatures, definitions and imports stay verbatim.

The node's proof and proof_origin now describe the completed implementation.
The local proof context is recorded in
`coord/changes/H9-finite-free-resolution-scalar-proof.md`; no consumers are adapted.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.FiniteFreeResolution.finiteFreeResolution_tensor`
(node `lem-sfb-ringed-finite-free-resolution-tensor`).
Added zero holes; zero sorries remain in the delivered module. This is a proof,
not a decomposition. The three other original theorem proofs are retained.
No new modules or nodes are introduced. The completed module compiled through
lcompile.py in 59.2 seconds; the delivery preflight checks the final clean source.

## No longer needed

None. No imports, modules or dependency nodes are removed. The proof follows the
existing seven-step plan and uses its existing bounded-flat and fixed-tensor results.
Mathlib's single-factor tensor collapse supplies the total-complex identification.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The rank bound `hrank` is
redundant for this proof because the supplied zero-term bound `hbound` proves
boundedness and the coordinate isomorphisms determine the terms; its public binder
is preserved. The scalar calculation works for arbitrary N and for rank zero,
without a point of the site or surjectivity of arbitrary sheaf maps on sections.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
