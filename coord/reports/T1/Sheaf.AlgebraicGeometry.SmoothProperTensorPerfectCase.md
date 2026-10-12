## What changed
Reduced `smoothProper_tensor_perfect_case` to two named intermediate theorems. The main theorem now combines their conclusions by a complete Lean proof. Added imports for the two intermediate modules.

## Proved and sorry left
The target theorem `AlgebraicGeometry.smoothProper_tensor_perfect_case` is proved from the two intermediate declarations. Sorry remains in `smoothProper_tensor_perfect_case_data` and `smoothProper_tensor_perfect_case_core`, each with its own node.

## No longer needed
No imports or DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong
The original node's two long proof steps require substantial constructions absent from the available library; they were split into the data and fixed-data comparison claims.

## New nodes
`lem-sc-smooth-proper-tensor-perfect-case-data` and `lem-sc-smooth-proper-tensor-perfect-case-core`.

## Second reading by T1

1. Compared the delivered item module with the repository version; the target signature and hypotheses are unchanged. Verdict: pass.
2. Compiled all three delivered modules with lcompile; there are no compiler errors, forbidden declarations, or unsplit sorries beyond the two named intermediate theorems. Verdict: pass.
3. Checked the two split statements against their Lean signatures and DAG records, and verified their source and node metadata. Verdict: pass.
4. Checked the proof route: the target combines exactly the data and core intermediate results, and the unit remains sk-thm-picard-duality; no imports were removable. Verdict: pass.
5. Added the required search records and proof-step metadata to both new nodes; no existing declarations were altered. Verdict: pass.

Changed line wrapping in the two new modules, completed both DAG nodes signatures, proof-step metadata, dependency sets, and Mathlib search records, and added this second-reading report.
