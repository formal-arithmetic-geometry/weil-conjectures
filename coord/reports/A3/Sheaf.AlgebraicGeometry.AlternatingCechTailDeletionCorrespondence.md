## What changed

Replaced the proof of `cechTailDeletionJunction` with a finite-index proof. The proof
uses the basic deletion identities, explicit `succAbove` case splits, and uniqueness of
stable sorting. The correspondence theorem remains assembled from the two component
lemmas as before. Added only proof imports for finite tuple sorting and finite deletion
maps.

## Proved and sorry left

`cechTailDeletionJunction` and `cechTailDeletionCorrespondence` are proved. The
strictly smaller construction lemma `cechTailDeletionBasic` remains `sorry` (node
`lem-pc-alternating-cech-tail-deletion-basic`), since its deletion/insertion bijection
requires the full finite permutation construction.

## No longer needed

No stated proof-dependency nodes or imports were pruned; both basic deletion and
junction nodes are needed by the final correspondence.

## Where the brief, the DAG or earlier work was wrong

The DAG's junction step is mathematically correct but its terse description hides the
needed recovery of the deleted stable rank. The proof makes that rank explicit through
stable-sort uniqueness and the restriction identity.

## Second reading by A3

1. Compared the delivered module with the repository version. Existing declaration signatures and definitions are unchanged; only proof imports and proof bodies differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles cleanly, with the only remaining `sorry` being the named `cechTailDeletionBasic`. No forbidden declarations or sorry in definitions were introduced. Verdict: pass.
3. Checked the split-off junction statement and its proof dependencies against the DAG and source description. It is a genuine strictly smaller consequence of the basic deletion identities, and the correspondence statement is unchanged and assembled from the two component results. Verdict: pass.
4. Read the proof from the target downward. It uses the basic deletion identities, finite permutation deletion, and stable-sort uniqueness; the unused helper `stable_before` was removed. The two added imports are proof-only and required. No further imports or nodes can be pruned. Verdict: pass.
5. Checked the realized unit route and DAG proof dependencies: the basic deletion result feeds the junction identity, which feeds the final correspondence, exactly as recorded. Verdict: pass.

Changed only the proof module by removing the unused private helper; no statements, definitions, DAG nodes, or imports visible to downstream modules were changed.
