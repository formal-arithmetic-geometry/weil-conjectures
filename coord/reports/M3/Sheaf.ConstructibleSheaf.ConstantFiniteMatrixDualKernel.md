## What changed
Added `ConstantFiniteMatrixDualKernelAux`, splitting the finite-free categorical kernel comparison from the final `ModuleCat.kernelIsoKer` identification. The target theorem now composes the auxiliary isomorphism with the mapped kernel isomorphism.

## Proved and sorry left
`nonempty_constantFiniteMatrixDualKernelIso` is proved. `constantFiniteMatrixDualKernelIso_aux` remains as one named sorry, with node `lem-weil-pbc-constant-finite-matrix-dual-kernel-aux`.

## No longer needed
None; all original imports remain required by the auxiliary statement or target.

## Where the brief, the DAG or earlier work was wrong
The original DAG demanded a multi-page finite-free categorical argument in one theorem. It did not expose the categorical-kernel substep as a separate node, so this delivery adds that strictly simpler intermediate statement.

## New nodes
`lem-weil-pbc-constant-finite-matrix-dual-kernel-aux`, stated in `ConstantFiniteMatrixDualKernelAux.lean`.

## Earlier second reading (a previous round; superseded)
The target proof compiles and preserves the exact original signature. The auxiliary statement is strictly simpler: it stops at the categorical ModuleCat kernel, and the target closes the remaining step with `ModuleCat.kernelIsoKer`.

## Second reading by M3

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged; only the proof body and the proof-only import of the auxiliary module were added.
2. Compiled both delivered modules with `lcompile.py --all`. They compile cleanly. The target theorem has no `sorry`; the only remaining `sorry` is the named auxiliary theorem, with its matching split node. No forbidden declarations or hollow definitions were introduced.
3. Checked the auxiliary statement against the categorical kernel step and `ModuleCat.kernelIsoKer`. It is true, strictly weaker than the target, and needed for the reduction; it does not merely restate the target. The node and Lean declaration agree.
4. The proof uses the auxiliary theorem and then `ModuleCat.kernelIsoKer`; all original public imports remain needed for the statements or auxiliary route. No prior proof dependency can be pruned from the delivered target module.
5. The unit route is preserved: the auxiliary node realizes the finite-free categorical-kernel substep, and the target composes it with the explicit module-kernel isomorphism as recorded in the DAG.

Changed during second reading: added this review section only. No Lean statements, definitions, or DAG proof data required repair.
