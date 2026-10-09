# Stage 1 report: `lem-weil-pbc-etale-free-sheaf-constructible`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-free-sheaf-constructible.json`: repaired split of Stacks Lemma 03S8 (Tag 03S8), part (3), with five proof steps and existing support-node citations.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-stratified-finite.json`: one new unsplit reusable node for Lemma 03S9 (Tag 03S9), with self-contained node citations and three Mathlib search kinds.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-finite-pushforward-locally-constant.json`: new unsplit self-contained module clause of Lemma 03RU (Tag 03RU), with all required node citations and three Mathlib search kinds.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-shriek-base-change-modules.json`: new unsplit self-contained module-form Lemma 03S6 (Tag 03S6) node.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-shriek-star-finite-modules.json`: new unsplit self-contained module-form Lemma 03S7 (Tag 03S7) node.
- `coord/reports/F1/lem-weil-pbc-etale-free-sheaf-constructible.md`: this report.

## Attachments

- `lem-weil-pbc-inverse-image-free-etale-module` supplies the inverse-image/free-module pullback identification and the existing module form of the Tag 03S6 extension-by-zero base-change statement.
- `def-weil-pbc-finite-etale-trace` supplies the existing finite-etale restriction/trace interface used for the Tag 03S7 comparison.
- `lemma-weil-pbc-constructible-finite-pushforward` supplies the existing Tag 03RU finite-pushforward constructibility statement.

## WANTED

None.

## Corrections and findings

- The prior delivery's 03S6 and 03S7 citations were too general for arbitrary finite module $M$. They are now represented by self-contained module-form nodes with exact tags and all relevant site, module, inverse-image, extension, direct-image, finite-etale, and fibre-product citations.
- The new 03S9 and narrow 03RU module-clause nodes remain self-contained. The broad constructible finite-pushforward node is deliberately absent because it depends back on this item and creates an eight-node cycle.
- Step 2 no longer argues about the unrelated representable sheaf of sets $h_U$. It states the required pullback of the module sheaf along each immersion $X_i\\to X$ and cites the inverse-image/free-etale-module node.
- Exact Stacks tags 03S9, 03S6, 03S7, 03RU, and 03S8 are present in the new node statement or proof source places. No statement or unit route was changed.

## Unfinished

The new 03S9, 03S6 module-form, 03S7 module-form, and 03RU module-clause nodes remain `unsplit` and are queued for later Stage 1 work. No Lean was written or compiled.

Validation: `python3 tools/review_split.py lem-weil-pbc-etale-free-sheaf-constructible` passes. On the current base, `python3 tools/check_dag.py` reports the pre-existing eight-node cycle and reachability notices; this delivery adds no cycle.

## Review by F1

I reviewed the repaired item against Stacks Lemma 03S8 (Tag 03S8), part (3), and its proof. Step 1 uses the self-contained Tag 03S9 node. Step 2 now cites the self-contained module-form 03S6 node, so it applies to a general finite $\\Lambda$-module $M$, not only the free module case. Step 3 cites the self-contained module-form 03S7 node for $\\pi_!M\\cong\\pi_*M$. Step 4 cites the narrow self-contained 03RU module-clause node, avoiding the broad constructible finite-pushforward node's dependency cycle. Step 5 applies the project's constructible-sheaf definition on the small etale site. All four new support statements have exact Stacks tags, complete node citations, and LeanSearch, Loogle, and Mathlib grep records. The delivery contains only the item, these four new nodes, and this report; `review_split.py` passes and `check_dag.py` reports zero cycles.
