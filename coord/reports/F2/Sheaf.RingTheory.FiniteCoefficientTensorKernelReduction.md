## What changed
Added the quotient-vanishing intermediate theorem and proved the original inclusion from it using Mathlib's quotient zero characterization. Removed two unused proof-only imports.

## Proved and sorry left
The original `RingHom.finite_coefficient_tensor_kernel_reduction` is proved. The intermediate `RingHom.finite_coefficient_tensor_kernel_reduction_quotient` remains sorry, isolating the closed-fibre tensor calculation; node `lem-weil-pbc-finite-coefficient-tensor-kernel-reduction-quotient` records it.

## No longer needed
`Mathlib.RingTheory.Flat.Equalizer` and `Mathlib.LinearAlgebra.Quotient.Defs` were not needed (their declarations are available through the remaining imports). The original proof dependencies remain required by the intermediate calculation.

## Where the brief, the DAG or earlier work was wrong
The DAG's three elementary steps conceal the full closed-fibre calculation. It is split into a quotient-vanishing theorem so the final inclusion proof is kernel-checked Lean.

## New nodes
`lem-weil-pbc-finite-coefficient-tensor-kernel-reduction-quotient` in the sandbox DAG records the remaining intermediate theorem.

## Earlier second reading (a previous round; superseded)
The quotient lemma is a strict intermediate formulation of the closed-fibre calculation; the parent inclusion follows by `Submodule.Quotient.mk_eq_zero`. The remaining sorry is exactly the tensor and residue argument described in the node.


## Second reading by F2

1. I compared the delivered module with the repository version. The existing target declaration has the same signature byte for byte; the only interface addition is the separately named quotient theorem documented in the report and node.
2. I compiled the module with `lcompile.py`; it is error-free. There is no axiom, unsafe declaration, or hollow definition. The sole remaining `sorry` is the named quotient theorem and is documented with its source and proof plan.
3. I searched the library and Mathlib for an existing closed-fibre kernel result. No duplicate declaration was found; the theorem is a strict intermediate conclusion used by the target proof.
4. The proof follows Mathlib's quotient characterization for the final inclusion. The quotient calculation remains explicitly isolated because its tensor and residue argument is not available as a proved library result.
5. The unit route is unchanged: the target still uses the flat closed-fibre calculation, with the quotient theorem realizing that intermediate step. The DAG node and Lean declaration agree on the remaining hole.

I removed the two unused imports listed above and left the quotient calculation as the single documented split-off theorem.
