## What changed
Split the construction into two strictly smaller public theorems. `exists_galoisPointAction` now combines the core action/formula theorem with the open-stabilizer theorem. The sandbox adds `GaloisPointActionCore.lean` and `GaloisPointActionOpen.lean` and imports them from the target module; all three files compile.

## Proved and sorry left
The target theorem `exists_galoisPointAction` is proved from the two intermediate declarations. The declarations `exists_galoisPointAction_core` (node `lem-exc-galois-point-action-core`) and `galoisPointAction_open_stabilizers` (node `lem-exc-galois-point-action-open`) remain `sorry` and are strictly smaller components of the argument.

## No longer needed
Removed direct imports of `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints` and `WeilConjectures.Mathlib.FieldTheory.IsSepClosed` from the target module. The residue-field module remains needed by the core construction.

## Where the brief, the DAG or earlier work was wrong
The original module's proof plan requires extension and residue-field arguments that are not available as completed declarations. No statement was changed.

## New nodes
`lem-exc-galois-point-action-core` records the action and displayed formula. `lem-exc-galois-point-action-open` records openness of stabilizers for an already constructed action. Both follow Tag 03QW and compile as separate modules.

## Earlier second reading (a previous round; superseded)
A second worker should verify that the target is unchanged, that each intermediate theorem is a strict reduction, and that the unit route remains represented by the two component nodes.

## Second reading by U1

1. **Target and declarations.** Compared `GaloisPointAction.lean` with the repository version. The theorem signature of `exists_galoisPointAction` is byte-for-byte unchanged; only its proof and proof dependencies changed. The two added declarations have distinct, strictly smaller conclusions: the core theorem supplies the action and formula, while the open theorem supplies only openness for an already supplied action.

2. **Compilation and proof hygiene.** Compiled all three modules with `python3 /home/ubuntu/weil-launcher/lcompile.py --all ...`; all compiled successfully. The target proof contains no `sorry`; the only remaining `sorry`s are the two named split-off theorems, each public, documented with source and proof outline, and represented by a DAG node. No axioms, unsafe declarations, opaque definitions, or hollow definitions were added.

3. **Statement review.** Checked the intermediate signatures against the target's quantified hypotheses and conclusions. The core theorem is exactly the target's existential action/formula component with openness removed. The open theorem keeps the same field hypotheses and action formula as assumptions and concludes exactly the target's stabilizer openness component. No hypothesis was added to the target and no conclusion was weakened.

4. **Search and imports.** Searched the repository and available declaration search for an existing Galois action or open-stabilizer theorem; no matching declaration was found. The target now imports the two proof modules privately. The core module retains the residue-field and separable-closure imports needed by its statement/proof plan; the target's former direct imports are removed and recorded as no longer needed.

5. **DAG and unit route.** Verified that the target node's `proof`, `proof_deps`, and `proof_origin` describe the proof now written, and that both new nodes carry the same chapter and unit (`sk-prop-h2`). The unit route is preserved through the two component nodes; no unrelated node is introduced.

Changed: added `GaloisPointActionCore.lean` and `GaloisPointActionOpen.lean`, updated the target proof and imports, updated the three corresponding DAG nodes, and recorded the removed direct imports. The target hole was closed; two strictly smaller component holes remain: `exists_galoisPointAction_core` (`lem-exc-galois-point-action-core`) and `galoisPointAction_open_stabilizers` (`lem-exc-galois-point-action-open`). No additional holes were introduced.
