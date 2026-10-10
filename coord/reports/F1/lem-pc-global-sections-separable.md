1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-global-sections-separable.json`: statement, split proof, Mathlib searches, and blueprint metadata.
   - `dag/nodes/sec-picard-framework/lem-pc-proper-geometrically-reduced-global-sections-separable.json`: new unsplit statement node; Mathlib verdict no match.

2. Attachments: none. No sorry-free slopmaster2 declaration states the item exactly; the keyword and blueprint-tag searches found no declaration.

3. WANTED: none.

4. The item source and the new node source were checked against Stacks `literature/stacks-project/varieties.tex`, Lemma 0BUG, clause (4). I also read the existing statements of `lem-pc-projective-proper` and `sbc-lem-smooth-geometrically-reduced`: the first supplies properness from projectivity and the second supplies geometrically reduced fibres from smoothness. Step 1 uses exactly those two facts and the smooth-projective-curve definition. Step 2 uses the new generalized 0BUG statement, whose hypotheses are exactly properness, geometric reducedness, and the assumed field structure on global sections. The generalized node was created only after searches through all DAG nodes, blueprint references, and the Lean source found no existing node or declaration. I checked the edge case `X = P^1_k`, where the global sections are `k` and the conclusion is immediate. I corrected the copied item's stale `created.item` metadata and made the generalized node's blueprint `via` point to this item.

5. No proof was left in Lean; the generalized theorem is intentionally statement-only for a later stage-1 split.

## Review by F1

I reviewed the item file, the parent blueprint node `lem-pc-ample-positive-degree`, the unit route in `sk-thm-picard-rr`, and the cited DAG statements. The first proof step explicitly establishes both hypotheses needed by the generalized theorem: projectivity gives properness, and smoothness gives geometric reducedness of the sole fibre over `Spec k`. The second step passes the exact global-sections field extension named in the item to the generalized clause and takes its exact separability conclusion. Every non-elementary fact is cited in `citations.json` with text copied verbatim from its node statement. The Lean source was searched for the item id, blueprint tag, and relevant global-sections/separability names; no exact sorry-free declaration exists. Mathlib searches were recorded for both nodes using LeanSearch, Loogle, and source grep, with no match.
