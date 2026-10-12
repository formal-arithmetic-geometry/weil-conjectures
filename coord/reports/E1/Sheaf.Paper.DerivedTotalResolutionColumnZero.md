## What changed

Replaced the proof of `total_resolution_column_zero_surjective` with the explicit quotient-by-boundaries argument following the finite-support reduction in [Stacks Tag 09IZ](https://stacks.math.columbia.edu/tag/09IZ). Added the proof-only imports `Sheaf.Paper.TotalResolutionCycleReduction` and `Mathlib.Algebra.Category.ModuleCat.Abelian`. All existing signatures and public imports remain byte for byte unchanged. The new module states only the finite-support cycle reduction.

## Proved and sorry left

Hole closed: `WeilConjectures.DerivedTotalResolution.total_resolution_column_zero_surjective` (node `lem-pc-derived-total-resolution-column-zero`). Its quotient argument is proved in Lean: lift along homologyπ, reduce the cycle, use monicity of iCycles and naturality, and kill the boundary using toCycles_comp_homologyπ.

Hole added and left: `WeilConjectures.DerivedTotalResolution.total_resolution_column_zero_cycle_reduction` (node `lem-pc-derived-total-resolution-column-zero-cycle-reduction`). This is the finite-support induction, the first three steps of the old proof plan; its docstring gives the full mathematical argument. One original hole closed and one lower hole added: a decomposition, net zero, not a completed proof of the original theorem. The theorem still depends on sorryAx through that lower statement.

The draft's `total_resolution_surjective_of_cycle_reduction` hole and node were removed after its argument was proved and inlined into the item. They were never part of the repository baseline.

## No longer needed

No original proof dependencies or imports were pruned (the old proof_deps was empty). No library module is claimed pruned. The draft-only generic quotient helper and its node are no longer delivered; the draft's unnecessary public ModuleCat.Abelian import was replaced by a proof-only import in the item.

## Where the brief, the DAG or earlier work was wrong

The draft lacked complete proof docstrings for its holes, and its existing-node update was outside dag/nodes, so deliver3.py would not have delivered it. The second reading repaired both problems. Generic search summaries and a placeholder proof step were replaced by the actual searches and finite-support proof steps. The local literature checkout lacks homology.tex; the second reader checked the official Tag 09IZ page directly.

## New nodes

`lem-pc-derived-total-resolution-column-zero-cycle-reduction`, in `Sheaf.Paper.TotalResolutionCycleReduction`: the cycle-level finite-support normalization, leaving the quotient step to the proved item. No statement or definition change records are needed.

## Second reading by E1

1. PASS: diff against the repository shows only proof changes and two plain imports in the existing module. The existing theorem signature, namespace, universes, docstring, and public imports are unchanged; no definitions were changed and no change record is needed.
2. PASS: both delivered modules compile with lcompile.py. The only sorry is the named cycle-reduction theorem. There are no axioms, unsafe/opaque declarations, foreign implementations, or definitions containing sorry. Explicit #print axioms checks show only propext, Classical.choice, Quot.sound and the expected sorryAx from the open reduction; the delivery tool also probes all declarations.
3. PASS: the remaining split is the finite-support induction, strictly the cycle-normalization part of the old argument, with the quotient argument actually proved in the item. Checked zero cycles, support entirely in column zero (b = 0), and a largest index r = 1: exactness is used at p = -2, so the strict p < -1 hypothesis suffices. For general r, exactness is used at p = -(r+1). Signed correction terms have degree n-1, and no vertical boundedness is assumed. The coproduct supplies finite support. The full induction and accumulation of the boundary primitive are documented. LeanSearch returned Internal Server Error (recorded as unavailable). Independent leanfinder, loogle and grep searches, plus reading neighboring library declarations, found no existing total-cycle normalization result. The generic quotient lemma was closed and inlined rather than left as a hole.
4. PASS: the proof takes the existing Mathlib quotient route after the sourced cycle normalization; it uses no other open library theorem. Original proof_deps is empty, so the No longer needed list is complete. The assigned unit's realized fields are empty and unchanged; no realized unit step or chapter route was bypassed. The supplied finite-support route is retained.
5. PASS: the existing node's actual delivered proof and proof_deps name the cycle-reduction node and the explicit quotient argument. The new node matches the Lean statement, contains source, statement dependencies, search evidence, provenance, chapter/unit and lean records, and gives the finite-support proof steps. The existing-node update now lies under dag/nodes where the tool reads it.

Changes in this reading: proved and inlined the generic quotient argument; removed its draft helper and node; added the complete cycle-reduction proof docstring; corrected proof-only import visibility; repaired and relocated the existing-node metadata; replaced new-node search and proof placeholders; corrected this report's hole accounting.
