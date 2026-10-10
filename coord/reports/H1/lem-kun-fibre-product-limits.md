1. Files written:
   - `dag/nodes/sec-smooth-purity/lem-kun-fibre-product-limits.json`: item, statement split into two elementary universal-property steps; Mathlib searches recorded, no Mathlib leaf.
   - `citations.json`: empty, because both proof steps use only the definitions/universal properties introduced in the item and are marked elementary.
2. Attachments: none.
3. WANTED: none. The imported source path is not present in this checkout; the existing DAG records the source as Stacks Categories Tag 002M, which is the cited mathematical source for the universal-property argument.
4. What was wrong in the imported node: its proof was a single incomplete paragraph (`elementary: null`) that asserted the two representability descriptions without spelling out the two directions or why the canonical map is the resulting isomorphism. I replaced it with two complete elementary steps. No statement change was needed. No duplicate node was found in the DAG or blueprint, and no sorry-free Lean declaration with this item tag or statement was found.
5. What I could not finish: no project Lean declaration exists for this imported item, so there is no attachment. Mathlib searches found only general pullback and limit-cone APIs, not this comparison theorem; LeanSearch was unavailable and is recorded as such.

## Review by H1

I read the item node, its unit `sk-prop-sf-kunneth-ordinary`, and the existing use sites in `lem-kun-0f09`, `lem-kun-0f1i-normal`, and `lem-kun-0f1h`. Those use sites require precisely the canonical isomorphism between the inverse limit of fibre products and the fibre product of inverse limits. I also read the existing G1 node `lem-weil-pbc-limit-fibre-products`, which identifies the source as Stacks Categories Tag 002M and uses this item for its limit comparison.

Step 1 uses only the universal properties of an inverse limit and of each fibre product: it explicitly introduces the compatible triples and checks both compatibility equations. Step 2 uses the same two universal properties in the opposite order, then checks that the canonical comparison sends each triple componentwise and therefore induces the identity on the represented sets; this supplies the inverse and proves isomorphism. Both are genuinely short definition-level arguments, so they are marked elementary and require no node citations; `citations.json` is consequently empty. I verified that all hypotheses in the statement are used only to ensure the indicated limits and fibre products exist. I tested the description on a constant system and on a singleton index, where the comparison is visibly the identity. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; the first three found only general APIs and LeanSearch was unavailable.
## Second reading by H1

- Item statement: checked against Categories Tag 002M (label `categories-lemma-colimits-commute`) and Schemes Tag 01JL; the comparison is correct, with structural maps and compatibility explicit.
- Step 1: checked against the universal properties of [def-pc-fibre-product] and categorical limits; the compatible-triple description is elementary and complete.
- Step 2: checked against the same universal properties and the canonical comparison; the componentwise identity argument gives the inverse and is elementary.
- New nodes: none; no child statement requires a separate B1-B7 audit.
- Existing-node search: searched the DAG and blueprint for the comparison and found no duplicate; Mathlib searches remain recorded in `searches.jsonl`, with no exact theorem.
- Changes: corrected the source from the blueprint markdown to `categories.tex` with Tags 002M and 01JL; added definition dependencies and explicit structural-map compatibility; filled the blueprint ancestry and `same_as` fields.
