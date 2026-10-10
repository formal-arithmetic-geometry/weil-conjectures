# Delivery report

1. Files written:

   - `dag/nodes/sec-picard-framework/def-sc-rational-section-divisor.json` — existing definition node, marked `split`; no new nodes; Mathlib verdict: no match.

2. Attachments: none.

3. WANTED: none. The cited Stacks source is the obtained Stacks Project source recorded by the project; the local checkout used for source inspection was `/home/ubuntu/c1-stacks-review/divisors.tex`.

4. What was checked: the statement was read against the parent unit `sk-thm-picard-rr` and the parent node `lem-sc-line-bundle-rational-section`. Stacks Tags 01X5, 02SF, 02MD, and 0BE6 support the generic-stalk interpretation of meromorphic sections, the order from a local generator, the DVR specialization on a smooth curve, and the divisor sum. The statement introduces every ambient object and cites the generic stalk, invertible-module, smooth-curve-local-ring, order, and divisor nodes. Independence of the local generator and finite support are facts of `lem-sc-rational-section-order`, so they remain statement dependencies rather than hidden proof steps. The definition has no proof to split and requires no smaller child node. Lean/source searches found no sorry-free declaration for this notion and no Mathlib algebraic-geometry divisor analogue; the only search hits were analytic divisor APIs.

5. Nothing remains unfinished.

## Review by K1

I checked the copied node against its blueprint origin and its unit route. The definition is exactly the terminology used by the parent rational-section lemma: a rational section is an element of the generic stalk, its order at a closed point is computed by expressing it relative to a local generator and applying the normalized valuation, and its divisor is the finite formal sum of those orders. The statement explicitly delegates generator independence and finite support to `lem-sc-rational-section-order`, and all other non-elementary notions are present in `stmt_deps`. I searched the DAG and blueprint for duplicate statements, searched the source checkout for an existing Lean declaration, and recorded the three required Mathlib searches (LeanSearch, LeanFinder, and Mathlib grep), all with no algebraic-geometry match. Since this is a definition, there are no proof steps or proof dependencies to add; the node is therefore complete as a stage-1 split.
