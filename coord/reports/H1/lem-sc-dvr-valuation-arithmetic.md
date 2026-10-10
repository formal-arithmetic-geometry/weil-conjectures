Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-dvr-valuation-arithmetic.json` (statement split; three proof steps).
- `dag/nodes/sec-curve-estimates/lem-sc-add-valuation-laws.json` (Mathlib leaf; generic additive valuation laws).
- `citations.json` (verbatim quotes for all step dependencies).

Attachments: none.  WANTED: `literature/stacks-project/algebra.tex`, Algebra Definition 00IE and the valuation identities used in Varieties Lemma 09N5, is not present in this checkout; the item follows the source location already recorded in the imported node.

The imported item had an empty proof. I split it into the product law, power law, and unequal-value sum law. The generic laws are stated by Mathlib's `AddValuation.map_mul`, `AddValuation.map_pow`, and `AddValuation.map_add_of_distinct_val`; the bundled normalized integer-valued statement is not itself a Mathlib declaration. No statement change was made to the item.

## Review by H1

I read the imported item and the upstream `lem-sc-jacobson-denominator-function-field` proof, where this lemma is used in the induction step of Stacks Varieties Lemma 09N5 after replacing an element by a power and adding a second element. The item statement introduces the normalized valuation, fraction field, nonzero elements, and all three identities. The new leaf states exactly the generic additive-valuation laws and was checked against Mathlib `Mathlib/RingTheory/Valuation/Basic.lean` declarations `AddValuation.map_mul` (line 1161), `AddValuation.map_pow` (line 1193), and `AddValuation.map_add_of_distinct_val` (line 1262).

Step 1 uses the DVR definition and the leaf's multiplicative law; after restricting the additive valuation to the fraction field and using the normalized integer codomain, this is exactly `v(ab)=v(a)+v(b)`. Step 2 uses the same two statements and specializes the power law to a positive natural exponent, identifying scalar multiplication in `Z` with `N v(a)`. Step 3 uses the DVR definition and the leaf's unequal-value sum law; the order on the normalized value group is the integer order, so the generic `min` is the item's `min`. These are not marked elementary because each uses the valuation interface and the normalization specialization.

I checked the edge cases conceptually: exponent `N=1` reduces to the original element, and unequal valuations exclude cancellation (for example, in `k(t)` with the `t`-adic valuation, `v(t)=1`, `v(1)=0`, and `v(t+1)=0`). The item has no Lean declaration in `weil-src-slopmaster2`; the Mathlib searches were run for both the item and the new leaf, with LeanSearch recorded as unavailable and LeanFinder/grep results recorded in each node.
