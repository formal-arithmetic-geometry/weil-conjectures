# Delivery report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-sc-noetherian-cohomology-vanishing-abelian-dim-one.json`: split statement; no Mathlib match.
   - `dag/nodes/sec-curve-estimates/lem-sc-noetherian-topological-cohomology-vanishing.json`: unsplit statement; no Mathlib match.
   - `citations.json` and this report.
2. Attachments: none. No sorry-free Lean declaration states either statement exactly; the similarly named scheme-module declaration is sorry-backed and has different hypotheses.
3. WANTED: none; the Stacks source is represented in the repository's imported literature metadata and existing nodes.
4. The item was unsplit. I searched the whole DAG, blueprint references, and the Lean source. The existing `lem-sc-zariski-dimension-bound` is scheme-specific, so it cannot supply the topological-space hypothesis of this item. I created the strictly more general statement node for Proposition 02UZ and kept it statement-only. The target proof specializes its finite dimension bound with `d=1`, `q=2`; the inequality `2>1` is elementary.
5. I tested the boundary cases conceptually: a one-point Noetherian space has no cohomology in degree 2, the empty space is included by the Noetherian-space theorem, and a dimension-one space is exactly the stated bound. No additional hypothesis is used.

## Review by F1

I read the target source citation (Stacks Proposition 02UZ as specialized in the blueprint ancestor's Lemma 09NY proof) and the existing DAG node `lem-sc-zariski-dimension-bound`. The latter states the result only for a Noetherian scheme and Zariski cohomology, so I did not cite it for this topological-space target. I searched the entire DAG and blueprint for Proposition 02UZ and for matching Noetherian-space/cohomology statements; no exact node existed. I also searched the Lean source and Mathlib by natural-language search, semantic search, and source grep; only a sorry-backed scheme-module theorem appeared.

The new node states the full 02UZ hypothesis and conclusion, including the definition of Noetherianity and the finite topological dimension, and has no proof sketch because it is an unsplit node. Step 1 of the item cites that node, and its verbatim statement in `citations.json` supplies exactly the Noetherian, dimension, sheaf, and vanishing facts used. The specialization checks the hypotheses one by one and the elementary inequality `2>1`; no other fact is hidden in the step. I checked the empty and zero-dimensional cases as boundary cases and verified that the target's cohomology notion is the same `[def-sc-topological-abelian-cohomology]` notion named by the generalized node.
