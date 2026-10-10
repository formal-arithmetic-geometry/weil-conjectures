1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-supported-factor-through-thick.json`: statement split, no new nodes, Mathlib searches found no matching theorem.

2. Attachments: none.

3. WANTED: `literature/stacks-project/derived.tex`, Tag 09SP, because the checkout contains only the citation index; the split follows the imported Tag 09SP proof description.

4. The item was unsplit and has no exact sorry-free Lean declaration. I searched the whole project source for the item id and for the factor-through/thick-closure terminology, and searched the DAG and blueprint for Tag 09SP and the same statement. No duplicate node or exact declaration was found. The statement was retained unchanged, including the explicit absence of a generation hypothesis. The proof now follows the two-part structure of Tag 09SP: compactness gives finite support at the initial coproduct, and induction across each distinguished triangle uses a finite-support connecting map and a cone; the final step checks closure under the stated thick operations. The only non-elementary generic fact used by the induction is the existing node `lem-weil-pbc-hom-into-triangle-exact`, whose statement supplies exactly the Hom factorization used. The finite-support assertion is the definition of compactness from `def-pc-compact-object`.

## Review by H1

I checked the item source and its ancestor reference in `lem-sc-finite-duality`, and read the consumer step in `lem-sc-pseudo-coherent-support-annihilation`: it applies this lemma only to a one-generator sequence whose successive cones are coproducts of shifts. I read `def-pc-compact-object` and verified that its coproduct Hom bijection is precisely what the initial finite-support and connecting-map arguments require. I also read `lem-weil-pbc-hom-into-triangle-exact`; its clause (ii) states the exact factorization through the first object of a distinguished triangle, which is the fact used in step 2, so the citation quote is verbatim. The induction's cone construction is the standard Tag 09SP construction, and step 3 records only closure operations explicitly present in the item's definition of thick subcategory. I tested edge cases conceptually: an empty/zero map factors through the zero thick object, n=1 is the finite-support base case, and repeated transitions accumulate only finitely many generator summands. Mathlib searches were rerun with LeanFinder, Loogle, grep, and LeanSearch (LeanSearch unavailable); no matching Mathlib theorem was found.

## Second reading by H1

- Item statement: checked against `/home/ubuntu/c1-stacks-review/derived.tex`, Tag 09SP (`lemma-factor-through`), including arbitrary-coproduct stages, compact source, finite thick closure, and the fact that generation is unused in this lemma; verdict pass.
- Step 1: checked against the Tag 09SP base case and `def-pc-compact-object`; finite support gives the stated finite sum and the thick closure supplies shifts and finite sums; verdict pass.
- Step 2: checked line by line against the Tag 09SP induction proof; finite-support connecting map, TR3 triangle morphisms, induction on the middle map, cone triangle, correction by a lift through `X_n`, and final finite direct sum are explicit. The cited `def-weil-triangulated-category`, `def-pc-compact-object`, and `lem-weil-pbc-hom-into-triangle-exact` statements provide these inputs; verdict pass after repair.
- Step 3: checked against the finite thick closure definition in the item and the conclusion of Tag 09SP; closure under the listed operations justifies the finite union of indices; verdict pass.
- New-node audit: no child nodes were created; the item is the only split node, and its statement cites definition nodes for its notions. The blueprint ancestor and `same_as: []` were checked with `tools/blueprint_refs.py`; verdict pass.
- Edge cases: the zero morphism factors through the zero object, `n=1` is the finite-support base case, and a singleton field or empty index family introduces no generation assumption; verdict pass.
- Changed: corrected `created.item` to `lem-sc-supported-factor-through-thick`, expanded step 2 to the explicit Tag 09SP induction, added its TR3 dependency and proof dependency, and added verbatim TR3 citation text. The source checkout lacks the TeX file, so the fetched copy `/home/ubuntu/c1-stacks-review/derived.tex` was used.
