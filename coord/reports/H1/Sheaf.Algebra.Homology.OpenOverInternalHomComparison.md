## What changed

Replaced the prior construction and its false split-off naturality theorem with a direct proof using the existing `AlgebraicGeometry.internalHom_restrict_scheme` theorem for restriction to `V`, mapped through the over-`W` functor and composed with `overHomObjIso_naturality`. Removed the unused `InternalHomOverEquiv` import. Updated the target node's proof route and dependencies; removed the split node `new-t4-open-over-internal-hom-comparison-naturality`.

## Proved and sorry left

The target `CategoryTheory.openOver_internalHom_comparison` is proved. No `sorry` remains in the delivered module, and no new hole was added. The previously split theorem was removed because its arbitrary-family statement was false.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.InternalHomOverEquiv` and the node `new-t4-open-over-internal-hom-comparison-naturality`.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced `openOver_internalHom_comparison_naturality` with an arbitrary isomorphism family `e`; no naturality hypothesis constrained `e`, so the statement is false. The target proof instead uses the already proved natural comparison theorem `lem-sc-internal-hom-restrict-scheme`.

## Second reading by H1

1. Compared the delivered module with the repository version. The target signature is byte-for-byte unchanged; the false intermediate declaration is removed and the proof-only import set is reduced.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The module contains no `sorry`, forbidden declarations, or hollow definitions. The proof uses only the existing comparison theorem and naturality lemma.
3. Checked the former split statement against edge cases and its quantification over arbitrary `e`; it is not true, so its node and declaration were removed rather than retained.
4. Checked the route and pruning. The unit-level target remains the same; the proof dependency route now records `lem-sc-internal-hom-restrict-scheme` and `lem-sc-internal-hom-over-naturality`, and the unused import/node are removed.
5. Checked the target node and Lean proof agree: the updated node records the direct composition route and its actual dependencies; no new node remains.

Changed the proof, imports, target node metadata, report, and removed the false split node.
