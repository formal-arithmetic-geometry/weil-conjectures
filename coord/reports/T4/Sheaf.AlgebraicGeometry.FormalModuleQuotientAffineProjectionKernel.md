## What changed

Filled `AlgebraicGeometry.formalModuleQuotient_affine_projection_kernel` with a complete proof.
The proof computes the affine product range using tensor sections, applies the affine
cokernel-image kernel formula, identifies the ideal power through `hJ`, and transports
membership across the tilde global-sections isomorphism. Added proof-only imports for
quasi-coherent cokernel-image, tensor sections, ideal-sheaf affine formulas, and quasi-coherent cokernels/kernels.

## Proved and sorry left

Closed the `sorry` in `formalModuleQuotient_affine_projection_kernel`. No `sorry` remains.

## No longer needed

No existing import or DAG dependency was removed. The plan is retained.
An exploratory import of `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` was
removed after compilation confirmed it was redundant; it was never a dependency of
this item's original node. No node/module is pruned from the original route.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was accurate. The implementation needed an explicit local affine
product-range lemma because the corresponding helper in the ideal-times module is private.

## Second reading by T4

1. Compared the delivered module with the repository version. The theorem statement and all existing declaration signatures are unchanged; only the proof and proof-only imports differ.
2. Compiled the module and the sandbox import closure with `lcompile.py`; both pass with no errors, and the delivered module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
3. Checked the proof route and declarations against the DAG and library search results. No split-off statements were added, so there are no new theorem statements requiring separate nodes.
4. The proof uses the stated affine ideal-times, tensor-sections, cokernel-image, and tilde/global-sections ingredients. The imports are exactly those needed by the proof; no additional pruning was identified.
5. The unit route is preserved: the affine range computation, cokernel-image kernel identification, ideal-power transport, and tilde-unit transport all occur in the delivered proof, agreeing with the node's `proof` and `proof_deps`.

Changed during second reading: added this review record only. No Lean code, declarations, DAG nodes, or imports were changed after the first reading.

