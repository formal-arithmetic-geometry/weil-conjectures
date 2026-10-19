# Stage-1 worker report: lem-coef-joyal-small-test-universe-invariance

## Files written

- `dag/nodes/sec-six-functors/lem-coef-joyal-small-test-universe-invariance.json`: item, now split with six proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement fragments for every node used by every proof step.
- `report.md`: this report and the signed review below.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, the item id, and the small-quasicategory/universe terminology. No sorry-free project declaration states this item exactly. The nearby Joyal declarations concern model-structure tests and interval fibrations; they do not state universe invariance.

## WANTED

WANTED: an archived copy of Cisinski, `CatLR.pdf`, for the universe refinement of Theorem 3.6.8(iii), printed pp.115–116. The source URL and the item’s original source description are retained; the proof is marked agent-written.

## What was wrong or incomplete

The imported item was an unsplit statement with an empty proof. I filled its proof without changing the statement, hypotheses, source metadata, inherited Mathlib searches, or blueprint ancestry. The key existing dependency is `lem-coef-small-inner-horn-completion`: for a U-small simplicial subset X of a V-small quasicategory C it gives a U-small quasicategory RX, the inclusion X to RX, and extension of maps RX to C by the actual restriction map’s lifting property against all monomorphisms.

The reverse implication is proved by reducing every U-small family of diagrams, edge representatives, and finite 2-simplex relation chains in the hFun categories to one U-small simplicial subset X of C. Applying the assumed equivalence to RX gives essential surjectivity, fullness, and faithfulness, and postcomposition with the extension RX to C transfers those conclusions to C. The forward implication is the universe inclusion. Empty simplicial sets and empty quasicategories are explicitly included in the completion and quantifier argument.

No new statement duplicates an existing node: the completion lemma is strictly smaller (it constructs RX and extension lifting), while this item compares the two quantifier ranges for hFun equivalences. No statement dispute or forbidden SGA source occurred.

## Review by NN

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B–E. I read the current item node, the `sec-six-functors` chapter, the `sk-prop-sf-biduality-general` unit record, and the ancestor binding `prop-coef-integral-exceptional-adjoint`. The item’s existing Mathlib search records were reused only after reading their result text; they all correctly report no matching Mathlib comparison theorem. I also searched the whole DAG and both blueprint snapshots for this item and for a small-horn/universe comparison duplicate.

For step 1, the definition of U-smallness and the nested-universe inclusion make the larger-test implication immediate, including the empty case. Steps 2 and 3 use exactly the statements of `lem-coef-small-inner-horn-completion`: its RX is U-small and quasicategorical, and its restriction map into any V-small quasicategory has the right lifting property against every degreewise monomorphism. I checked that the square with left side empty to a point gives the extension map RX to C, and that the degreewise image closure of a U-small family remains U-small.

Step 4 applies hypothesis (i) to the U-small quasicategory RX. Essential surjectivity in the ordinary hFun category gives an extension of an A-diagram up to the required isomorphism; postcomposition with the chosen RX-to-C extension preserves that isomorphism. Step 5 uses the same equivalence’s fullness for a finite edge-word representative of an A-morphism. Step 6 uses faithfulness after putting both B-morphism representatives and the finite 2-simplex relation chain witnessing equality of their A-restrictions into the same X. These uses match the item’s explicit definition of hS as words in edges modulo the 2-simplex relations; no proof-only property of a cited node is used.

I checked all hypotheses in each application: A and B are U-small, RX is a U-small quasicategory, C is an arbitrary V-small quasicategory with no local-smallness assumption, and all factorization/extension maps are actual simplicial maps. The empty X, A, B, and C cases remain covered. All six proof steps are below the long-step threshold, `proof_deps` is exactly the union of their `uses`, and `citations.json` quotes are verbatim substrings of the cited statements. No Lean file was written or compiled, and only the sandbox was modified.

## Unfinished work

None for this one-level split. The cited completion node remains an independent unsplit/split DAG item as required by stage 1.
