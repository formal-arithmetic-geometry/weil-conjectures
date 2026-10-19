## Files written

- `dag/nodes/sec-six-functors/lem-coef-triangular-top-deletion-anodyne.json`: repaired the returned split, with the original statement and ancestry preserved. No new nodes; no Mathlib leaves.
- `citations.json`: regenerated against the current repository for all nine proof steps.

The sandbox also retains `searches.jsonl` and has `verify_matching.py`, a finite mathematical verification script, plus the sandbox-only editing script `repair.py`. These are not DAG delivery files.

## Attachments

No attachment. The earlier search for `(blueprint: lem-coef-triangular-top-deletion-anodyne)` found none; I repeated the id and notion searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and found no declaration of the inclusion. The exact upstream master is only reference material, and its sorry declarations would not establish an attachment.

## Sources and retained searches

I read the source `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, the chapter and unit records, the item's statement, and the parent `lem-coef-terminal-comparison-coherence` (particularly step 3). The blueprint paragraph is the integral adjunction calculation, not a published proof of this interval-poset assertion. The item's ancestry records its extraction as an agent auxiliary for coherent terminal comparisons; the proof remains explicitly agent-written. No Stacks tag or SGA result is claimed for this combinatorics. The parent step requires exactly the retained marked inclusion, including deletion of `(n,n)` and constant-first marking.

I read the retained Mathlib search results. The inherited Q66 searches and the four logged Q08 searches are preserved in the node and `searches.jsonl`; the Q08 semantic hits are ordinary nerves, nondegenerate-chain criteria and horns, and the source grep has no marked-anodyne or interval-poset match. Loogle reported unknown identifier `marked`, with no hits; that query is not evidence that the theorem is absent by itself. The LeanFinder, LeanSearch and source results supply the other searches. Since neither the statement nor the Mathlib search question changed, those searches were not repeated. No new node requires a fresh search. The whole-blueprint searches for `triangular` and `interval poset` produced no equivalent imported statement.

WANTED: none. This is a direct finite combinatorial proof; it does not appeal to unavailable literature.

## Repair of the return

The returned head is `a5dd45de83`. I compared the retained item with the current read-only repository: the statement, source, dependencies and blueprint ancestry agree; the differences are the previous proof, proof origin, split report and split status. The first required dry run of the retained version exited successfully at `d900ee3ec5`. That mechanical result did not answer the mathematical return. The proof and this report are now substantively replaced, with searches retained.

E5/D5: steps 1–3 now characterize all full-support paths and define a total involutive matching. At the first `D` or `HV`, the rule exchanges `D` and `HV`; if neither occurs, it adds/removes the final `H`. The insertion at `D` is explicitly `(i,j-1)`, with a fixed horizontal priority. No reverse scan, unavailable-face test or fallback branch remains. The argument shows why each full-support chain is covered and why the forbidden all-`V` terminal path cannot occur.

The ancestral-order gap is repaired in steps 4–6. Pairs are ordered by upper dimension, then the lexicographic vertex list. Every other full-support facet either is an upper chain of smaller dimension or has an upper partner with a strictly smaller vertex list. The proof classifies all deletions, including a `VH` that overlaps the selected `HV`, and deletion of its final `V` target. The horn intersection is then a direct induction on this explicit finite order. Thus an insertion's other faces are available when its pair is reached, and no dimension-increase claim is used as an acyclicity argument.

Step 7 proves the horn index lies in `[1,d]` and derives, rather than assumes, that `r=d` is an appended constant-first `H`. Step 8 treats the dimension-two edge markings explicitly: a final horn can introduce an unmarked `[0,1]`, which must be marked only if its first endpoints agree; then `[0,2]` and `[1,2]` are already marked and triangle cancellation supplies `[0,1]`. Consecutive-edge composition is not used in place of cancellation. Step 9 carries the global conclusion and is marked non-elementary, repairing C2.

The earlier counts were only half the full-support cells and did not verify a shelling. The new script checks partner membership, involutivity, codimension one, every other facet's earlier rank and actual presence, the missing facet's absence, all its subfaces' presence, horn indices, and marking cases, and verifies exact exhaustion. It independently enumerates all strict poset chains for n=1 through 6 to check the path characterization, and performs the full matching/attachment checks for n=1 through 10. The pair counts are 1,3,8,20,49,119,288,696,1681,4059; these counts are now incidental to the checked conditions. The proof supplies the all-n argument separately.

## Not duplicates

No new nodes. The existing lifting calculus supplies generators and closure, not this interval-poset shelling. The existing triangle-cancellation statement supplies the initial-edge marking map, not the shelling. No statement is moved into a new clause node. The local path and facet computations are written out as the item's argument; no abstract discrete-Morse or shelling theorem is silently invoked.

## Review by Q08

I read all of sections B–E of `coord/delivery-errors.md` with the item and the three cited statements open. The statement is true; no statement dispute or correction is needed. I retained n>=1, the exact interval inequalities, the union over all proper endpoint subsets, removal of only `(n,n)`, and the induced constant-first marking. No new-node B-format, duplicate-tag or Mathlib-leaf obligations arise. No route changes or tool_uses are needed: all cited nodes are in this unit.

For step 1, the nerve statement of `def-cbc-enhanced-diagrams-cones` gives strict poset chains after discarding degeneracies. The endpoint-skip arguments prove the path description in both directions; the final width bound and initial `(0,n)` are justified explicitly. Steps 2 and 3 use only this chain convention and the path description already proved. Inserting the H corner is strictly inside the interval at a D, and appending a diagonal has i<n, so neither leaves Q_n. Feature preservation in both directions and the feature-free end cases prove involutivity rather than assuming it.

For steps 4 and 5 I checked every possible adjacent pair of path letters. Only HV and VH can be merged while preserving support. The same-dimensional rank cases replace a V corner by an H corner, whose first endpoint is strictly smaller; every remaining full-support facet is already an upper chain of smaller dimension. The initial-vertex deletion loses an extreme endpoint. For step 6 the cited definition really describes the horn as the union of all facets except the selected one; the direct finite induction proves this intersection and the two-cell attachment, with no additional shelling lemma cited or hidden.

For step 7 I read generators (i) and (ii) in `lem-coef-marked-anodyne-lifting-calculus`, including the dimension-one final generator and its marking. The pivot cannot be the minimum, and the terminal pivot is precisely the last H target. A horn of dimension at least three contains every edge, so its extra induced markings are inherited by the pushout. For step 8 I read the exact displayed map of `lem-coef-marked-triangle-cancellation`: it adds `[0,1]` when `[0,2]` and `[1,2]` are marked. Its W is generated by exactly the four families of the calculus statement. The inner two-horn adds only an unmarked diagonal; the final two-horn cases have the required final marking, and cancellation marks no edge outside the target marking.

For step 9 I checked the stated pushout and finite-composition closure against the calculus node and the cancellation node. The description of degreewise union and of union markings proves the actual marked pushout without citing only a definition for a separate theorem. Finiteness and exhaustive pairing give the specified target, not merely a subcomplex. All proof steps, especially this conclusion, are non-elementary. Every step is shorter than 2000 characters; each carries a direct portion of the explicit matching argument rather than an omitted independent lemma.

I checked n=1 directly: D_1 is the vertex `(0,0)` and the single marked final-one-horn attachment adds `(0,1)->(0,0)`. For n=2 the rank order is the triangles `((0,2),(0,1),(0,0))`, `((0,2),(0,1),(1,1))`, `((0,2),(1,2),(1,1))`, with horn indices 2,1,2. The first triangle needs the initial-edge cancellation; the last introduces a nonconstant-first edge and needs no extra marking. For n>=3 the exhaustive tests include diagonal D steps, overlaps HVH, and adjacent-width terminal chains. They do not replace the dimension/lexicographic proof.

All citation entries were regenerated, with one per node per step, and their quotations checked as verbatim substrings of the current cited statements. I wrote only in the assigned sandbox. No Lean, compiler, Lake, shared repository, live project or launcher files were changed.

## Unfinished

No mathematical repair point remains. The final repaired dry run and push are the delivery steps after this report.
