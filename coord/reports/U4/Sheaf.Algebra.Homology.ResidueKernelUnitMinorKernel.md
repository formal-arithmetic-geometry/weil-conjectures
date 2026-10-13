## What changed
Reduced `ModuleCat.residue_kernel_unit_minor_normal_form` to two named intermediate theorems: localization freeness and the matrix unit-minor normalization over a local ring. Both intermediate proofs remain explicit `sorry` holes with source and proof plans in their docstrings.

## Proved and sorry left
The target theorem is now proved by applying the two intermediate declarations. Sorry remains in `ModuleCat.residue_kernel_unit_minor_base_change_free` and `ModuleCat.residue_kernel_unit_minor_matrix_core`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt stopped at the matrix argument. The stage brief requires splitting that argument into named intermediate statements; the reduction now compiles.

## New nodes
`new-residue-kernel-unit-minor-base-change-free` and `new-residue-kernel-unit-minor-matrix-core`.

## Second reading by U4

1. Compared the delivered item module with the repository version; the existing target signature is unchanged and only its proof/imports were added.
2. Compiled all three sandbox modules successfully; the two split declarations are explicit named `sorry` theorems, with no hollow definitions or forbidden declarations.
3. Checked both split statements against their Lean signatures and supplied DAG nodes, sources, proof plans, and Mathlib search records; both are strictly simpler reductions of the matrix argument.
4. Checked the proof route: the target invokes the localization-freeness reduction and then the unit-minor matrix normalization, preserving the unit route. No imports were removable.
5. Checked node metadata and report consistency; repaired missing blueprint tags, node statement metadata, proof steps, and search records.

Changed the two split-node docstrings and DAG records, and added this second-reading report. The target theorem remains proved; the two intermediate declarations remain intentionally open with their documented Stacks Project proof plans.
