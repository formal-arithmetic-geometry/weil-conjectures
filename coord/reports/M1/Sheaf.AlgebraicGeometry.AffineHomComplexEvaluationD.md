## What changed
Added the degreewise decomposition theorem `affine_hom_complex_d_components` and used it to prove `affine_hom_complex_d` by homological-complex extensionality. The component theorem is the sole remaining sorry and records the termwise affine calculation.

## Proved and sorry left
`affine_hom_complex_d` is proved. `affine_hom_complex_d_components` remains sorry, with node `lem-sc-affine-hom-complex-evaluation-d-components`.

## Earlier second reading (a previous round; superseded)
The decomposition theorem is strictly degreewise, while `affine_hom_complex_d` is proved by genuine homological-complex extensionality. The original target signature is unchanged.

## No longer needed
None; both stated proof-dependency imports are used by the component theorem's planned termwise construction.

## Where the brief, the DAG or earlier work was wrong
The original node bundled the termwise construction and chain-map extensionality into one hole; the delivery separates these strictly, proving the extensionality glue in Lean.

## New nodes
`lem-sc-affine-hom-complex-evaluation-d-components` records the degreewise termwise comparison left for a subsequent worker.

## Second reading by M1

1. **Visible changes and statements.** Compared the delivered module with the repository version. The existing theorem `affine_hom_complex_d` has the same signature byte for byte; the only new declaration is the explicitly split degreewise theorem recorded by the new DAG node.

2. **Proof checks.** Compiled the delivered module with `lcompile.py`; it compiles without errors. There is no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The only remaining `sorry` is the named theorem `affine_hom_complex_d_components`, with its source and DAG node recorded above.

3. **New statement.** Checked the degreewise theorem's hypotheses and conclusion against the original target. It is a strict componentwise decomposition of the original equality, with the same chain isomorphism witness and no added hypotheses or weakened conclusion; its termwise affine construction is the intended remaining proof obligation.

4. **Pruning and route.** The proved theorem uses `HomologicalComplex.hom_ext` to reassemble the component equalities, preserving the unit's affine Hom-complex route. No imports or proof dependencies can be removed while the component theorem remains the stated source of the witness.

5. **DAG agreement.** The new node's Lean declaration, statement, source, proof plan, and `proof_deps` match the split theorem in the module. The original node's route is retained through the component theorem and the extensionality step.

Changed in this second reading: added this review record only; no Lean statements or proofs were altered.
