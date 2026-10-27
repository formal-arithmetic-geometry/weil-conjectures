## What changed

Filled the proof of `WeilConjectures.AdicQbarRealization.stageTensor_existsUnique`
in `Sheaf.Paper.CommonStageInclusionTensorComparison`. Unfolding the existing
`stageTensorFormula` exposes the canonical composite inverse, which supplies the
witness. Heterogeneous reflexivity proves its normalization; `eq_of_heq` proves
uniqueness. All signatures, definitions, options, docstrings and imports are
unchanged. Updated the owning node's proof, proof dependencies and proof origin
to record this direct construction.

Validation: the complete module compiled through `lcompile.py` with exit code 0
in 25.4 seconds, below the 60-second limit.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.AdicQbarRealization.stageTensor_existsUnique`
(node `def-sf-common-stage-inclusion-tensor-comparison`).

No holes remain in the item; no holes or split-off statements were added.
The theorem uses the recorded common-stage tensor and scalar-unit constructions;
it does not claim to close holes in their dependencies.

## No longer needed

None. The sole public import `Sheaf.Paper.DerivedPullbackTensorHom` is required
by the unchanged statements and formula. No module or DAG dependency is pruned.
The proof needs no import of the nearby `CommonStageInclusionTensorModel` module:
the existing formula already contains its relevant composite.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The node had no numbered proof steps; its existing
Lean docstring gives the direct existence-and-uniqueness argument now implemented.
The identity coefficient-extension case is covered without assuming its scalar
unit is definitionally the identity. The unit's route is unchanged.

Searches: msearch Loogle `HEq, ExistsUnique` returned no hits; LeanFinder for the
unique isomorphism heterogeneously equal to an explicit canonical isomorphism
returned generic isomorphism and cast APIs. Local searches found analogous
`HEq.rfl`/`eq_of_heq` uniqueness proofs and the finite-stage tensor model; no
additional lemma or construction was needed.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
