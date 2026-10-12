## What changed
Proved `CategoryTheory.Functor.cochainHypercohomologyLeftEdge_single` using the canonical single-complex edge comparison. Added the intermediate module `Sheaf.CategoryTheory.HypercohomologyLeftEdgeSingleAux` containing the single-complex comparison theorem (left as a named sorry). The main proof imports this auxiliary module.

## Proved and sorry left
The target theorem `cochainHypercohomologyLeftEdge_single` is proved. The auxiliary theorem `cochainHypercohomologyLeftEdge_single_aux` remains `sorry`, with node `lem-pc-hypercohomology-left-edge-single-aux`.

## No longer needed
No imports or existing nodes were pruned; the auxiliary statement is the only new dependency.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan omits the explicit intermediate single-complex edge comparison needed to avoid a circular import through `HypercohomologyLeftEdgeCanonical`; this delivery states that comparison as a separate lower theorem.


## New nodes
`lem-pc-hypercohomology-left-edge-single-aux`: `coord` node and module `lean/Sheaf/CategoryTheory/HypercohomologyLeftEdgeSingleAux.lean`.

## Second reading by G1

1. Compared the delivered item module with the repository version. The theorem signature is unchanged byte for byte; only its proof and the proof-only auxiliary import changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; both compile successfully without warnings. The item theorem has no `sorry`, while the named auxiliary theorem is the only remaining `sorry`. Verdict: pass.
3. Checked the auxiliary statement against the single-complex edge calculation and searched Mathlib and the repository with LeanSearch, Loogle, and grep. The statement is a strict intermediate comparison and is true as used. Verdict: pass.
4. Read the proof downward from the canonical cycle lift, through the auxiliary comparison, to the single-complex homology isomorphism. The unit route remains represented by the existing left-edge definition and no imports or nodes can be pruned. Verdict: pass.
5. Updated the auxiliary node's proof record and search record to match the delivered Lean declaration and proof dependency. Verdict: pass.

Changed the auxiliary docstring to include the required proof explanation, removed the unnecessary `simpa` warning, and corrected the auxiliary node's recorded signature and search entries.
