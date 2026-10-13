## What changed
Added a strict two-part decomposition in `Sheaf.AlgebraicGeometry.CoherentHomsOverOpen`: `coherent_homs_over_open_data` supplies the structural data and `coherent_homs_over_open_extension` supplies the extension clause. The target theorem is now proved by destructing the data and assembling the original conclusion. The two intermediate proofs remain named `sorry`s for parallel completion.

## Proved and sorry left
The target declaration `AlgebraicGeometry.Scheme.coherent_homs_over_open` is closed by a real assembly proof. The declarations `coherent_homs_over_open_data` and `coherent_homs_over_open_extension` remain `sorry`, with nodes `lem-weil-pbc-coherent-homs-over-open-data` and `lem-weil-pbc-coherent-homs-over-open-extension`.

## No longer needed
None. The existing imports remain the stated plan dependencies; no dependency was safely removable while retaining the exact structural statement.

## Where the brief, the DAG or earlier work was wrong
The DAG's thirteen-step geometric proof is too large to complete in one worker item. It was decomposed into two strict intermediate claims, preserving the exact target statement and leaving each genuine geometric part as a separately named node.

## New nodes
`def-weil-pbc-coherent-homs-over-open-data-structure`, `lem-weil-pbc-coherent-homs-over-open-data` and `lem-weil-pbc-coherent-homs-over-open-extension` are new strict intermediate nodes in the same module.

## Earlier second reading (a previous round; superseded)
The target signature is unchanged. The target proof is a genuine constructor assembly from the strict structural and extension parts; both remaining holes have their own nodes and are smaller parts of the original argument. The structure declaration is a data-only packaging definition.

## Second reading by A4

1. **No accidental visible changes.** Compared the delivered module with the repository version. The existing target declaration and all imported declarations retain byte-for-byte identical signatures; only the new packaging structure, two named intermediate declarations, their proofs, and proof-only metadata changed.

2. **Proof checks.** Compiled the module with `lcompile.py`; it compiles cleanly. The target has a real constructor assembly proof. The two remaining `sorry`s are named theorems with source and proof descriptions, and neither is inside a definition. No axiom, unsafe, opaque, extern, or implemented-by declaration was added.

3. **Statements and new nodes.** Checked both split statements against the target: the data theorem packages the first conjuncts and colimit data, while the extension theorem supplies only the final extension clause. They are true, strictly smaller than the target, and the node metadata now records their actual proof routes without a circular dependency on the target.

4. **Pruning and route.** The target's original imports remain in place because the structural theorem uses the geometric route and the unit's realized route is preserved. No import or existing node can be removed safely at this decomposition stage.

5. **DAG agreement.** Updated the two split nodes' proof steps and `proof_deps` to agree with the declarations and docstrings. The data node follows the geometric Steps 1--7 and 13; the extension node uses the data package and the elementwise filtered-colimit representation.

Changed the split theorem docstrings to include complete natural-language proof routes, repaired circular proof-dependency metadata, and added this second-reading record.
