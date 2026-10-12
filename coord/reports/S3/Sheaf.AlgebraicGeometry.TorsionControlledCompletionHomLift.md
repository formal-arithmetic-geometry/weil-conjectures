## What changed

Proved `AlgebraicGeometry.torsionControlled_completion_hom_lift` by reducing existence to the new strictly simpler theorem `torsionControlled_completion_hom_lift_exists` and proving uniqueness with `coherentMap_torsion_completion_ext`. Added the proof-only imports for these declarations. Added the existence theorem module and its DAG node.

## Proved and sorry left

Closed the sorry in `torsionControlled_completion_hom_lift`. The new declaration `torsionControlled_completion_hom_lift_exists` remains a sorry, with node `lem-weil-pbc-torsion-controlled-completion-hom-lift-exists`.

## No longer needed

Removed proof-plan imports `CoherentFormalModulesAffine`, `CoherentFiniteTypeLocallyNoetherian`, `FormalGlueingComplexExact`, and `GlueSheavesOfModules`; their declarations are encapsulated by the split existence theorem and are not needed by the completed target proof itself.

## Where the brief, the DAG or earlier work was wrong

The original node bundled affine/gluing existence and uniqueness into one theorem, while the existing completion extensionality theorem directly supplies uniqueness. The proof was therefore split into a strictly smaller existence statement.

## New nodes

`lem-weil-pbc-torsion-controlled-completion-hom-lift-exists`: existence half of the target lifting theorem, stated in `TorsionControlledCompletionHomLiftExists.lean`.

## Earlier second reading (a previous round; superseded)

Pending independent second reading. The target proof compiles, and the new existence statement is strictly weaker than the target and is exactly the affine-gluing existence step.

## Second reading by S3

1. Compared the delivered target module with the repository version. The theorem statement and all existing declaration signatures are unchanged; only proof imports and the proof body differ. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds with no errors. The target has no `sorry`; the existence theorem is the sole named split-off sorry. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked the split-off existence statement against the target hypotheses and conclusion. It is the strict existence half, while uniqueness is supplied by the existing extensionality theorem; its DAG node and docstring record the source and construction. Verdict: pass.
4. The proof follows the shortest available route: existence theorem followed by `coherentMap_torsion_completion_ext`; removed the affine/gluing proof-only imports and updated the target node proof dependencies accordingly. Verdict: pass.
5. The unit route remains represented by the existence node and target node, and DAG proof/proof_deps/proof_origin match the Lean proof. Verdict: pass.

Changed the target DAG node to record the two-step proof and pruned the four obsolete proof-only imports. No additional holes were introduced beyond the named existence theorem.
