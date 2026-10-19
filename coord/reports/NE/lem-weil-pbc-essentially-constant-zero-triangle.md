# Stage 1 report

1. Files written: `dag/nodes/sec-proper-base-change/lem-weil-pbc-essentially-constant-zero-triangle.json` (item, no new nodes); `citations.json`.
2. Attachments: none.
3. WANTED: none.
4. The imported item was unsplit. I checked the exact Stacks proof of Tag 0G3A in `literature/stacks-project/derived.tex` (lines 12416–12517). The statement is correct for inverse systems whose outer transition maps are eventually zero. I reused the existing DAG statements `def-weil-inverse-system`, `lem-weil-pbc-hom-out-of-triangle-exact`, `lem-weil-pbc-five-lemma`, `lem-pur-triangulated-hom-colimit-comparison`, and `lem-pur-essential-constant-pro-criterion-05py`; their statements supply the transition composition, Hom exactness, five lemma, Hom-colimit comparison, and the converse Hom-colimit criterion respectively. Step 1 verifies a common tail where both outer maps to a fixed level are zero. Step 2 applies the exact five-term Hom sequence and the five lemma. Step 3 applies the pro Hom-colimit criterion with value zero, whose factorization clause gives an eventually zero middle transition. Step 4 specializes to the chosen level. I ran the required LeanFinder, Loogle (including a second phrasing), grep, and LeanSearch Mathlib searches; LeanSearch was unavailable and is recorded by the search log. No source or statement correction was needed.

## Review by NE

I read the item, its chapter/unit records, the ancestor blueprint node, and the full Tag 0G3A proof. I checked every cited node's statement against the use in each step: the inverse-system composition law in Step 1; Hom exactness, filtered Hom comparison, and the five lemma in Step 2; and the Hom-colimit-to-essential-constancy criterion plus transition composition in Step 3. The fixed-level and common-tail hypotheses are explicitly quantified, and the last step correctly turns essential constancy with value zero into a zero transition at the chosen level. The split adds no duplicate child node and records the cross-unit Hom-colimit lemma as a declared tool use.

## Second reading by NE

- Statement: checked against derived.tex Tag 0G3A, lemma-essentially-constant-2-out-of-3, and the zero-valued specialization; correct, unchanged. Zero triangles and constant triangles over a field give the expected conclusion; at n=1 the same index choices work. Empty-scheme derived categories are zero and satisfy the statement. n=0 is outside the stated indexing. No statement dispute.
- Step 1: checked against def-weil-inverse-system and def-weil-triangulated-category; the chosen transition is a triangle morphism and its first square makes the required composite zero. PASS after repair.
- Step 2: checked clause (i) of lem-weil-pbc-hom-out-of-triangle-exact against Tag 0149, lemma-representable-homological; the distinguished triangle at m and W=B_n satisfy every hypothesis, giving precisely the factorization used. PASS after repair.
- Step 3: checked against the hypothesis at the new level m, the second triangle-morphism square, and def-weil-inverse-system; the displayed composite is zero by associativity and composition with zero. PASS after repair.
- Step 4: checked k>=m>=n and the universal quantifier in the item; PASS.
- New nodes: none; no new statements, definitions, duplicate nodes, or Mathlib leaves require review.

Changes and reasons:
- Replaced the fixed-level Hom-colimit argument: the original Step 1 only killed maps to n, whereas its Step 2 asserted vanishing of entire Hom-colimits without using hypotheses at all their levels. Moreover lem-pur-triangulated-hom-colimit-comparison compares components 1 and 2 to obtain component 3; its application to outer components would require an explicit rotation and a supplied zero comparison triangle. Its statement does not itself provide filtered-colimit exactness.
- Used the existing Hom-exactness clause directly to factor B_m -> B_n through C_m, then killed C_k -> C_m. This is the elementary zero-valued argument for the same Tag 0G3A specialization and stays on the unit route.
- Removed the unused five-lemma and two cross-unit pro/colimit dependencies, and their worker-written tool_uses. Updated the proof summary, provenance, and citations.json to the repaired steps; every retained citation quotes the complete actual statement.
- Read all five originally cited node statements before removal; their conclusions do not repair the fixed-level inference as originally written. Preserved the first worker sections as requested; the corrected proof and this section supersede their claims about the old argument.
- Independently searched the read-only slopmaster2 source by item id and pro-zero/Hom-exactness vocabulary: no finished declaration stating this item was found. Ran msearch.py grep with proZero|IsProZero|pro_zero|essentiallyConstant: zero Mathlib hits, recorded in searches.jsonl. No new node search records were invented.
