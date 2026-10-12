## What changed

Closed `CategoryTheory.exists_topological_cocycle_objectwise` using the existing
`CategoryTheory.exists_topological_leray_spectral_object_augmentation` theorem.
Instantiate its functors with canonical terminal-open cohomology, take the component
of its composite bottom-edge map, and simplify its cocycle formula along reflexive
functor identifications. Added only a proof import of
`Sheaf.Topology.TopologicalLeraySpectralObjectAugmentation` and updated the node's
proof route. The theorem signature and public imports are unchanged.

Scoped `linter.unusedVariables false` to this theorem alone, for the two unused
names of hypotheses bound inside its existing conclusion. This replaces the earlier
file-level suppression that preflight rejected. No file-level option is changed.
Removed the byte-identical augmentation module copy from the delivered set.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.exists_topological_cocycle_objectwise`
(node `lem-sc-topological-cocycle-objectwise`). No sorry remains in the item's module.
No holes or declarations were added and no new statements were split off.
The existing imported theorem
`CategoryTheory.exists_topological_leray_spectral_object_augmentation`
(node `lem-sc-topological-leray-spectral-object-augmentation`) remains sorry in the
library; this delivery proves the item from that previously stated theorem.

## No longer needed

No existing imports were removed: all three public imports support the unchanged
statement. The old direct proof dependencies
`def-sc-topological-abelian-cohomology`,
`def-weil-pbc-topological-inverse-image`, and
`lem-sc-topological-pushforward-injective` are replaced in this node's proof route by
`lem-sc-topological-leray-spectral-object-augmentation`. They are subsumed by the
augmentation theorem, not claimed to leave the targets' full import closure.
No modules are claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The planned direct resolution comparison is unnecessary here: the existing Leray
augmentation theorem already supplies the universal objectwise cocycle formula.
The earlier sandbox node retained the old proof prose despite changing dependencies;
its proof steps now describe the actual specialization and component extraction.
The earlier second-reading text claimed dry-run success despite the file-level option
rejection; that stale review was removed for a fresh independent second reading.
The unit `sk-thm-curveestimate` realizes only `thm-sc-proper-cohomology` and has no
realized proof-step nodes; this local change bypasses no unit statement or step.

## Second reading by Q2

1. Compared the delivered module with the repository version. The theorem signature,
   hypotheses, conclusion, and public imports are byte-for-byte unchanged; only the
   proof import, scoped linter option, and proof body differ. The node's proof route
   and dependencies match the proof.
2. Compiled the module with `lcompile.py`; it succeeds with no errors. There are no
   remaining `sorry`s, forbidden declarations, or hollow definitions in the module.
   The proof uses the existing augmentation theorem, whose open `sorry` is an
   explicitly imported dependency.
3. The proof adds no statements or nodes. The existing objectwise statement is used
   unchanged, and the specialization of the augmentation theorem is exactly the
   required cocycle formula; no weaker conclusion or extra hypothesis was introduced.
4. The augmentation theorem is the shortest available route and is already the
   stated proof dependency. The three original direct dependencies are no longer
   used by this proof, while all public imports remain necessary for the unchanged
   signature. No target-reachable module is claimed pruned.
5. The unit route is preserved: this theorem remains the objectwise cocycle node in
   `sk-thm-curveestimate`; no unit statement or realized step is bypassed.

Changed in this reading: added this independent review record only; no Lean code,
node statement, or dependency was changed.
