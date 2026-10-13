## What changed
Reduced `sectionRing_overlap_base_map` to a pointwise comparison theorem and compiled both modules.

## Proved and sorry left
`sectionRing_overlap_base_map` is proved from `sectionRing_overlap_base_map_pointwise`. The pointwise theorem remains `sorry` as the strictly simpler unresolved step.

## No longer needed
None; all original imports remain required by the statement.

## Where the brief, the DAG or earlier work was wrong
The original proof plan requires substantial Proj and stalk arguments; no existing theorem matching the pointwise comparison was found.

## New nodes
`lem-sc-section-ring-quotient-chart-overlap-base-map-pointwise` in the sandbox DAG records the pointwise intermediate theorem.

## Earlier second reading (a previous round; superseded)
Compiled successfully with the sandbox compiler; the pointwise intermediate is the only remaining hole.

## Second reading by V2

1. Compared the delivered base module with the repository version. The theorem signature is unchanged; the only existing declaration change is its proof, and the pointwise theorem is a new split-off declaration with a matching node.
2. Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the named pointwise theorem, and no forbidden declarations or hollow definitions were added.
3. Checked the pointwise statement and node metadata. The statement is the needed pointwise reduction, with the same hypotheses and conclusion as the target after extensionality; its node now records the exact Lean declaration and declaration name. No duplicate declaration was found in the repository or search results.
4. The base proof takes the shortest available reduction (topological and continuous-map extensionality followed by the pointwise node). The pointwise argument remains open because the required Proj and stalk comparison infrastructure is not available as a proved declaration. No imports were pruned: all public imports support the interface, and the pointwise module is proof-only imported.
5. The unit route is preserved: the target node is reduced through the pointwise comparison node, which is the stated intermediate step. No target or definition was changed.

Changed the pointwise docstring to satisfy the line-length convention and corrected the new node's Lean declaration metadata and exact statement. No holes were closed beyond the target reduction; one strictly simpler pointwise hole remains.
