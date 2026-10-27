## What changed

Proved `WeilConjectures.podNormalized_tensor_signed_shifts` by applying the already
stated `WeilConjectures.podReindexingTensorSignedShifts` to the supplied `A`, `hA`,
`T` and `hT`. Added its module as a private proof import. The existing theorem has
exactly the required generality, including every representative and integer shift.
Updated the item node's proof, proof dependencies and proof origin to record this
reuse. Existing signatures, definitions, docstrings and public imports are preserved.

Validation: lcompile.py compiled the delivered module successfully (exit 0, 9.1 s),
with no diagnostics. The delivery tool runs its required probe and preflight.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.podNormalized_tensor_signed_shifts`
(`lem-pod-normalized-tensor-signed-shifts`).
Added 0 holes; split off 0 statements. The delivered module has 0 textual holes.

This is a proof from the existing declared dependency
`WeilConjectures.podReindexingTensorSignedShifts`
(`lem-pod-reindexing-tensor-signed-shifts`), whose proof remains `sorry` in its
unchanged module. Thus the item closes a duplicate obligation; it does not claim
the underlying signed tensor construction is now free of all transitive holes.

## No longer needed

No imports removed and no modules withdrawn or globally pruned. The existing
public import is preserved as part of the module's public interface.

The direct proof dependencies
`lem-pod-reindexing-completion-unit-tensor`,
`def-pod-completion-reindex-shifts`,
`def-pod-completion-tensor-normalization` and
`def-pod-completion-reindex-models` are replaced by
`lem-pod-reindexing-tensor-signed-shifts`. The three definition nodes remain
statement dependencies and indirect dependencies of the reused theorem. The
completion-unit-tensor theorem is not used to choose an existential family in this
proof. Its module remains publicly imported; no claim of global pruning is made.
The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier report distinguished arbitrary normalized data from the particular
existential family produced by `podReindexingCompletionUnitTensor`. However,
`podReindexingTensorSignedShifts` already quantifies over arbitrary `D` and `T`
satisfying their laws and gives precisely this conclusion. Reusing it avoids
repeating the signed quotient-tower and Roos construction or introducing another
split. The import-direction check accepts the dependency and finds no cycle.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
