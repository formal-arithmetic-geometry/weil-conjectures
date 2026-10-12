## What changed
The module proves the boundary containment component directly using `filteredComplex_boundaries_le_cycles`, and combines it with the named intermediate comparison theorem. The remaining quotient and naturality construction is isolated in `filteredQuotient_comparisons_rest`.

The interface decomposition is recorded in `coord/changes/filteredQuotient_comparisons.md`.

## Proved and sorry left
The original declaration `filteredQuotient_comparisons` is reduced by a real proof to boundary containment plus the intermediate theorem. One sorry remains in `filteredQuotient_comparisons_rest`, node `lem-sp-filtered-quotient-comparisons-rest`.

## No longer needed
No imports were removed.

## Where the brief, the DAG or earlier work was wrong
The original node bundled the elementary boundary containment with the substantially larger comparison/naturality construction. This delivery splits that independent first step into a compiled proof and names the remaining construction explicitly.

## New nodes
`lem-sp-filtered-quotient-comparisons-rest` records the remaining quotient and naturality theorem and its postponed proof.

## Earlier second reading (a previous round; superseded)
The original theorem statement is unchanged. The new intermediate theorem is strictly simpler because it assumes all boundary containments and returns only the remaining comparison data.

## Second reading by K3
1. Compared the delivered module with the repository version. The existing theorem signature and all definitions are unchanged; only its proof and the named split theorem were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with only an unused `hr` warning. There are no forbidden declarations, and the only remaining `sorry` is the named split theorem. Verdict: pass.
3. Checked the split statement against the parent node and source. It is a strict decomposition: it assumes boundary containment and returns exactly the remaining quotient, representative, and naturality clauses. The statement is true as the stated categorical construction, with its source and node recorded. Verdict: pass.
4. Checked the proof route and imports. The boundary clause uses `filteredComplex_boundaries_le_cycles`; the parent then applies the split theorem. The unit route is preserved, and no import is demonstrably removable because the remaining theorem's public signature uses the imported categorical constructions. Verdict: pass.
5. Checked the DAG records and change record. The parent node's proof and dependencies match the Lean proof, and the split node has the required source, proof, dependencies, and Lean record. Verdict: pass.

Changed the accidental loss of the target theorem's doc-comment marker back to `/--`; no mathematical interface changed.
