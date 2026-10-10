1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-regular-meromorphic-section-exists.json`: split item, no Mathlib match.
- `citations.json`: empty citation list because the two source steps use no DAG node.

2. Attachments: none.

3. WANTED: none.

4. The source node cited obsolete numbering (02OZ as Lemma 31.5.10). The current Stacks page is Tag 0EMI, Lemma 31.25.4, and Tag 02OZ is the reduced-case wrapper; the statement itself remains the locally Noetherian no-embedded-points case. No sorry-free declaration in `WeilConjectures/` states this item (searched by item id and by meromorphic/generic-stalk terms). The existing DAG node `lem-sc-rational-functions-generic-stalks` concerns only the structure sheaf, so it cannot supply the invertible-module meromorphic-sheaf description; that fact is recorded as the new smaller statement-only node.

5. What was checked: I read the Stacks proof of 0EMI/02OZ and the existing generic-stalk and rational-function nodes. The preflight identified the initially drafted generic-product node as a clause-level restatement, so it was removed; the source argument is now carried directly by the item steps. Step 1 follows the source's rank-one generator choice and generic-point description. Step 2 checks injectivity componentwise because each chosen element is a generator. The properness and finite-dimension hypotheses are inherited from the item and are not needed by the stronger local Noetherian source lemma. Mathlib searches were run for the item and the discarded draft node; LeanSearch was unavailable. Small checks: for an integral affine scheme with L = O, the tuple is a nonzero element of the fraction field; for a finite disjoint union, the product map is componentwise injective.

## Review by E1

I checked the item against Stacks Divisors Tags 0EMI and 02OZ, including the hypothesis that X is locally Noetherian with no embedded points and L is invertible. Step 1 follows the source's generator choice and generic-point description. Step 2 performs the finite componentwise injectivity argument; the product-of-injective-maps observation is elementary. I verified the item has no project declaration with the blueprint tag or equivalent terms and recorded the required Mathlib searches, including unavailable LeanSearch.

## Second reading by E1

- Item statement: checked against Divisors Tag 0EMI, Lemma 31.25.4, and the Tag 02OZ wrapper; the locally Noetherian/no-embedded-points and invertible-module hypotheses agree, and the proper finite-dimensional hypotheses are inherited from the item context.
- Step 1: checked against the source proof and [lem-sc-rational-functions-generic-stalks]; the generic-point product is cited, and the transport from structure sheaf stalks to an invertible module is spelled out through local trivializations.
- Step 2: checked against the same product statement and the source's componentwise generator argument; the component maps and finite-product injectivity are explicit, with the latter elementary.
- New nodes: none; the only supporting fact needed is the existing generic-stalk product node, found by searching the whole DAG for `rational-functions-generic-stalks` and generic-point product statements.
- Small cases: for an integral affine scheme with the trivial invertible module, the construction is a nonzero element of the fraction field; for a finite disjoint union, the product map is componentwise injective; the empty scheme is vacuous.

Changes made: corrected the source place from the obsolete 02OZ numbering to current Tag 0EMI; added the existing generic-stalk product citation and proof dependency; expanded both steps to state the module transport and componentwise map. The base node's `created` metadata names the earlier worker item and is maintainer-owned, so it was left unchanged for the delivery tool to preserve.
