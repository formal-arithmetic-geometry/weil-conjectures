## What changed

The target theorem is proved by combining two strictly simpler named decomposition lemmas in the same module: `cechTailDeletionBasic` supplies the equivalence and the rank, restriction, and prefix identities; `cechTailDeletionJunction` supplies the junction-map equality from those identities. The decomposition lemmas remain `sorry` and have new DAG nodes. The target node proof dependencies and proof steps were updated accordingly.

## Proved and sorry left

Proved `cechTailDeletionCorrespondence` by applying the two decomposition lemmas and combining their conclusions. Sorries left: `cechTailDeletionBasic` (node `lem-pc-alternating-cech-tail-deletion-basic`) and `cechTailDeletionJunction` (node `lem-pc-alternating-cech-tail-deletion-junction`).

## No longer needed

No imports were removed. The original monolithic proof plan is replaced by the two decomposition nodes; no other stated nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The original node had a multi-page deletion/insertion argument but no intermediate Lean interfaces for its two independent parts. The target proof is therefore decomposed into the basic deletion identities and the junction identity, each strictly weaker than the target.

## New nodes

`lem-pc-alternating-cech-tail-deletion-basic` and `lem-pc-alternating-cech-tail-deletion-junction`, both declared in the target module and recorded under `dag/nodes/sec-picard-framework/`.

## Earlier second reading (a previous round; superseded)

The target signature is unchanged. Its proof combines the basic deletion identities and the junction identity. Both new statements are strict components of the target and retain the unit route; they are the only remaining holes.

## Second reading by U4

1. **Visible declarations and signatures.** Compared the delivered module with the repository version. The target declaration and the two existing index abbreviations are byte-for-byte unchanged; only the target proof and the two named decomposition theorems were added.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it is clean. The target proof contains no `sorry`; the only remaining holes are the two named split theorems, each with a source docstring and matching node. No forbidden declarations or hollow definitions were introduced.
3. **Split statements.** Checked the basic lemma and junction lemma against the target: the first supplies exactly the equivalence and four deletion identities, while the second supplies only the junction equality under those identities. Both are strictly weaker than the target and mathematically follow the labelled deletion construction; neither duplicates the target. Their DAG dependencies were corrected to avoid a circular dependency (basic -> sorting definitions; junction -> basic).
4. **Pruning.** The sorting-operator import is needed by the public abbreviations and split theorem statements, so no import can be removed. No obsolete proof dependency remains; the split-node proof metadata now follows the actual downward route.
5. **Unit route and DAG agreement.** The target proof applies the basic lemma and then the junction lemma exactly as recorded in its node. The unit route is preserved: this remains the unsigned labelled tail-deletion step for the Picard Cech argument, with no bypass of the unit-level statement.

Changed the two split-node dependency records to remove their circular reference to the target, and added this second-reading review. No statement or definition was changed.
