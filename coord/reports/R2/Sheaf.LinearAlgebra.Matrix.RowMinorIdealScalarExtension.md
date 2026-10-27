## What changed

Filled `Matrix.rowMinorIdeal_scalar_extension` without changing its signature.
The coordinate equivalence is Mathlib's `TensorProduct.piScalarRight`; its inverse
formula follows by decomposing a vector into its single-coordinate vectors.
`Submodule.baseChange_eq_span` and `Submodule.map_span` identify the image of the
tensored inclusion, without assuming it injective.

The ideal equality is proved for arbitrary `rowMinorIdeal n k` first. The image
of an old minor is a new minor by `RingHom.map_det`. For the converse, a private
proved multilinearity lemma extends ideal membership from tuples of generators
to tuples in their span, by finite-set induction and `Submodule.span_induction`.
A second private proved helper puts determinants with any chosen column subset
in the row-minor ideal. All helpers have complete proofs. Added only the private
proof import `Mathlib.LinearAlgebra.TensorProduct.Pi`. Updated the existing DAG
node's proof and proof origin to describe these arguments.

## Proved and sorry left

Closed the single original hole in `Matrix.rowMinorIdeal_scalar_extension`
(node `lem-trf-row-minor-ideal-scalar-extension`). Added zero holes and zero
split-off statements. No `sorry` remains in the delivered Lean module.
The launcher single-file compile passed without warnings in 2.6 seconds.
The delivery preflight supplies the declaration-by-declaration axiom checks.

## No longer needed

No imports, nodes, or modules are withdrawn. The four existing proof dependencies
remain relevant to the tensor coordinates, base change, free-coordinate
expansion, and determinant calculation. The explicit permutation reindexing of
the original plan is replaced by multilinearity and rowwise span induction;
no additional dependency was needed for it.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan is valid; Mathlib already
provides the tensor-coordinate equivalence and the submodule span description,
and its determinant multilinear interface avoids a manual Leibniz expansion.
The finite-coordinate induction covers an empty index set, so the tensor
formulas hold for `n = 0`. The ideal argument handles `n ≤ k` as the unit ideal,
and the final theorem handles `r > n` as the zero ideal. Neither flatness nor
finite generation of the relation submodule is used.

The search used the launcher LeanFinder query for arbitrary row-minor base
change, Loogle `MultilinearMap, Submodule.span`, and grep for `rowMinorIdeal`,
`piScalarRight`, and `baseChange_eq_span`. Their candidate declarations were read
in the pinned Mathlib; none proves the whole statement directly.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
