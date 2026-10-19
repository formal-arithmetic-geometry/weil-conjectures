1. Files written:
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-bounded-derived-tower-pro-zero.json` (split item; Mathlib no match).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-essentially-constant-zero-triangle.json` (statement-only node; Mathlib no match).
- `citations.json`.

2. Attachments: none.

3. WANTED: none.

4. The item had no finished declaration in the source. I split the Stacks Tag 0G3B proof into finite-degree stabilization, the existing truncation triangle, and induction using a new zero-valued two-out-of-three statement (Tag 0G3C). The statement and hypotheses were retained exactly. The Mathlib searches found only general triangulated exactness and t-structure lemmas, not the inverse-system result.

5. Nothing remains unfinished.

## Review by NI
I read the item node, the chapter and unit records, and the complete source passage for Tag 0G3B in `literature/stacks-project/derived.tex`, including the truncation induction and its reference to Tag 0G3C. I also read the existing node `lem-weil-pbc-truncation-triangle` and verified that its statement supplies the distinguished truncation triangle used in step 2. Step 1 is elementary finite stabilization over the bounded interval `[a,b]`; it uses only the item's hypotheses. Step 2 uses exactly the existing node's statement that a canonical truncation triangle is distinguished. Step 3 uses the new node's verbatim statement that an inverse system of distinguished triangles with eventually zero outer transition maps has eventually zero middle transitions. The induction base is the single-degree case, where the object is its cohomology placed in degree `a`; the induction step shortens the upper cohomological interval. I checked the hypotheses at each step, including vanishing outside `[a,b]`, the finite maximum over degrees, and the requirement `k >= n`. I tested edge cases `a=b` and the zero object system conceptually. The new node is not a duplicate: searches for Tag 0G3C, “essentially constant”, and “pro-zero” found no DAG node stating this zero-valued inverse-triangle result. All Mathlib searches were run and recorded in the node; LeanSearch was unavailable. The exact dependency phrases are recorded in `citations.json`.

## Not duplicates
lem-weil-pbc-essentially-constant-zero-triangle vs lem-weil-pbc-noetherian-koszul-augmentation-pro-zero: the new node states the general zero-valued two-out-of-three lemma for arbitrary inverse systems of distinguished triangles in a triangulated category, while the existing node states a specific Koszul augmentation cone tower over a Noetherian ring and merely cites Tag 0G3C as an input.

## Second reading by NI

- Item statement: checked hypothesis by hypothesis against Stacks Tag 0G3B (`lemma-essentially-constant-cohomology`) in `derived.tex`; bounded cohomology and degreewise eventual zero maps are the stated zero specialization.
- Step 1: checked against the finite-degree stabilization part of Tag 0G3B; the finite maximum argument and vanishing outside `[a,b]` are elementary.
- Step 2: checked against Tag 0G3B's truncation induction and the statement of `lem-sf-derived-truncation-triangle`; corrected the cited node and made explicit why the lower truncation is the single cohomology object.
- Step 3: checked against Tag 0G3B together with Tag 0G3A (`lemma-essentially-constant-2-out-of-3`) and `lem-sf-derived-concentrated-single`; the induction base and zero-valued two-out-of-three use exactly those statements.
- New node `lem-weil-pbc-essentially-constant-zero-triangle`: checked against Tag 0G3A, with inverse-system and triangulated-category definitions cited; its zero specialization is self-contained and no Mathlib declaration matches.
- Edge cases checked: `a=b`, the zero tower, and a field abelian category; all satisfy the hypotheses and conclusion.

Changes made: corrected the erroneous Tag 0G3C citation to Tag 0G3A; replaced the mismatched truncation citation with `lem-sf-derived-truncation-triangle`; added `def-weil-inverse-system` and `lem-sf-derived-concentrated-single` dependencies; repaired the item's `created.item` metadata; updated citations to verbatim node statements. Tag 0G3C is the distinct pro-isomorphism lemma and was not used.
