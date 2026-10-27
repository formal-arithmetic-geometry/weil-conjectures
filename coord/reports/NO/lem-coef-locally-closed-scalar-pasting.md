## Files written

- `dag/nodes/sec-six-functors/lem-coef-locally-closed-scalar-pasting.json`: item split into six proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim citations for the composite-adjunction counit statement used in steps 2, 3, and 6.

## Attachments

None. I searched `lean/WeilConjectures/` by the blueprint tag and by locally closed scalar, mate, and coefficient-pasting terminology; no sorry-free project declaration states this item.

## WANTED

None. The proof follows the existing master blueprint proof paragraph and the Stacks composite-counit lemma already recorded by the composite-adjunction node.

## What was wrong or needed repair

The imported item was unsplit even though its statement contains three coherence assertions. I retained its statement and dependencies exactly, and wrote the calculations rather than introducing nodes that merely restate those assertions. The proof now expands the locally closed counit through the closed and open counit equations, proves the successive coefficient cocycle by naturality of the closed comparison, and derives the further-closed-immersion formula from the closed composition cocycle. The final step spells out the triple composite counit. No cancellation of an exceptional comparison is used, so the stated absence of invertibility hypotheses is respected.

## What I could not finish

Nothing.

## Review by NO

I read the item node and its source `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-closed-shriek.md`, including the paragraph that supplies the locally closed factorization and coherence route. I also read the corresponding main-20261015 `sk-lem-sp-tower` statement and proof file, the existing definition node `def-weil-pbc-composite-adjunction`, and the statement-only nodes for closed transpose cocycles and open scalar adjunction counits. The latter two are assumptions in this item's statement; the item step uses only the formulas stated there.

Step 1 checks the domains, types, naturality, and the inverse formula for `c_h` directly from the definitions of `b_h` and `c_h`; it uses no non-elementary node. Steps 2 and 3 expand the actual counit of the composite adjunction, use naturality of the closed counit and of `e_j`, then apply the closed and open normalization equations appearing verbatim in the item statement. Their only cited node is `def-weil-pbc-composite-adjunction`, whose statement explicitly gives the composite counit `ε₂ ∘ H(ε₁)`, quoted in `citations.json`; I checked that the quote is an exact substring. Step 4 checks successive scalar change using the three stated cocycles and one naturality square, with all tensor associators identified as the input cocycles specify. Step 5 applies the stated closed-composition cocycle and functoriality of `R u_B^!`. Step 6 verifies the triple counit by applying the same composite-adjunction formula twice, and cites the same node with its exact counit sentence.

I tested edge cases in the written formulas: identity coefficient change gives the identity comparison, and the calculations never require `b_t` or `b_h` to be invertible. I searched the whole DAG and blueprint for duplicates; the existing locally closed etale lemma and open-scalar coherence lemma differ in category and hypotheses, while `lem-sfb-pasted-mates-counit-normalization` is a generic mate lemma rather than this conditional scalar-pasting assertion. Mathlib searches (LeanFinder, Loogle, LeanSearch, and source grep) were run and recorded in `mathlib_searches` and `searches.jsonl`; they found only generic composite-counit and mate-pasting declarations, so this item is not a Mathlib leaf.
