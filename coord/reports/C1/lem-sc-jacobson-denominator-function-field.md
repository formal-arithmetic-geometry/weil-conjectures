1. files written

`dag/nodes/sec-curve-estimates/lem-sc-jacobson-denominator-function-field.json`: target split, three proof steps.

`lem-sc-semilocal-dim-one-conductor` (statement, no Mathlib match): Stacks 09N2 conductor interface.

`lem-sc-semilocal-dedekind-dvr-reduction` (statement, no exact Mathlib match): semilocal Dedekind localization reduction.

`lem-sc-dvr-tensor-surjective-negative-valuation` (statement, no Mathlib match): Stacks 09N5 induction base case.

`lem-sc-dvr-valuation-arithmetic` (statement, generic Mathlib valuation facts only): normalized valuation arithmetic.

2. attachments

None. The slopmaster2 source has no declaration tagged `(blueprint: lem-sc-jacobson-denominator-function-field)` and no sorry-free declaration stating this item.

3. WANTED:

None. The Stacks sources used here are available in the local review checkout; no additional document was needed.

4. what was wrong or incomplete

The imported item had no proof split even though Varieties Lemma 09N5 has three distinct arguments: passing to integral closures and using the conductor, reducing semilocal Dedekind rings to DVRs, and the valuation induction. The source's conductor lemma and the valuation base case were not existing DAG nodes, so I added statement-only nodes after searching all DAG nodes, the blueprint, and the Lean source. I kept the target statement unchanged.

5. what I could not finish

No unresolved mathematical step remains at stage 1. The new support nodes are intentionally unsplit interfaces for later workers.

## Review by C1

I read the target source at Stacks Varieties Lemma 09N5 (`varieties-lemma-create-globally-generated`) and the preceding Varieties Lemma 09N2 (`varieties-lemma-semi-local-dimension-one-conductor`), including the paragraphs on integral closures, the DVR reduction, and induction on the number of valuations. I also read Algebra Definition 034W and Lemma 034X for the Dedekind localization facts and Definition 00IE for valuation arithmetic. I searched the whole DAG and blueprint for 09N2, 034X, the base case, and the valuation statement before creating the four support nodes; no node stated those facts as needed.

Step 1 cites the conductor node for exactly its assertion that a power of an element of the Jacobson radical of the integral closure, multiplied by any element of that closure, lies in the original ring. The remaining passage is the source's reduction: tensor surjectivity persists under an overring, and integral spectra are surjective. Step 2 cites the localization node, whose statement explicitly supplies finitely many maximal ideals, DVR localizations with fraction field K, and the Jacobson-radical equivalence. Step 3 cites the base-case node for the existence of a negative-valuation element and the valuation-arithmetic node for products, powers, and the unequal-value sum formula; the induction chooses a power so all earlier valuations are below those of y, then applies the stated minimum rule. I checked the hypotheses at each use: every B_i is a Noetherian one-dimensional semilocal domain with fraction field K, every tensor map is surjective, and the valuation list is finite. Small cases checked were r=1 (the base case) and r=2 with v_1(x)<0 and v_2(x)≥0, where x^N+y has the required two negative valuations. The item blueprint `from.place` was already the 09NB/09N5 sentence and `same_as` search returned no matches.
