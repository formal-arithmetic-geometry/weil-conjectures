## What changed
The target module now contains a compiling reduction of the one-point reconstruction theorem. Two named intermediate theorems split the field-theoretic reconstruction into selected-lift existence and propagation to all lifts; the target combines them by a real Lean proof. The intermediate theorem proofs remain `sorry` and are recorded as new DAG nodes.

## Proved and sorry left
The target `AlgebraicGeometry.Scheme.field_equivariant_germ_family_section_onePoint` is proved from the two intermediate declarations. The remaining sorries are `AlgebraicGeometry.Scheme.onePoint_selected_lift_section` (node `lem-exc-field-equivariant-germs-one-point-selected-lift`) and `AlgebraicGeometry.Scheme.onePoint_propagate_from_selected_lift` (node `lem-exc-field-equivariant-germs-one-point-propagation`).

## No longer needed
None; the stated proof-dependency imports remain available for the intermediate obligations.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt stopped before making a compilable reduction. The direct field-theoretic argument is substantial, but it can be represented as two strictly smaller obligations while the target proof itself is complete.

## New nodes
`lem-exc-field-equivariant-germs-one-point-selected-lift` records reconstruction at one chosen lift. `lem-exc-field-equivariant-germs-one-point-propagation` records propagation from that lift to every geometric lift.

## Second reading by V3

1. **Statements and interfaces.** Compared the delivered module with the repository version. The existing target signature is byte-for-byte unchanged; the two added declarations have signatures matching their intended strictly smaller obligations. Verdict: pass.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; the target proof is complete and the only remaining `sorry`s are the two named split-off obligations. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. **Split-off statements and nodes.** Checked both obligations against their docstrings and DAG records, and corrected each node's Lean declaration and verbatim statement to name the actual declaration. Verdict: pass.
4. **Pruning and imports.** The existing public and proof-only imports are still used by the module or its stated interfaces; no import can be removed without changing the available declarations. Verdict: pass.
5. **Unit route and DAG agreement.** The target node now records the actual reduction through selected-lift reconstruction followed by propagation, and both split nodes retain the unit `sk-prop-h2`. Verdict: pass.

Changed the two split-node `lean` records to the actual declarations and statements, and updated the target node's proof and `proof_deps` to match the compiled reduction. No Lean source changes were needed during second reading.
