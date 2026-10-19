# Stage-1 report: cor-rp-euler-product

## Files written

- `dag/nodes/sec-purity-real-sheaves/cor-rp-euler-product.json`: the item, a statement split into two proof steps; Mathlib searches found no match.
- `citations.json`: four verbatim node-statement quotations for the cited uses.
- No new DAG nodes were required: every non-elementary ingredient in the two steps already has an existing node.

## Attachments

`AlgebraicGeometry.WeilGroup.exists_eulerSeries_mul_eq_coe` is not an attachment: its source declaration in `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Rankin.lean:461-465` has `sorry` and states existence of a polynomial after multiplying the Euler series by the compact-top Frobenius characteristic polynomial, rather than the displayed Euler-product identity of this item.

## WANTED

None.

## What was wrong or incomplete in the imported item

The imported item was marked `imported` and had no Mathlib searches. Its Lean audit is `none`; the nearby Lean theorem is unfinished and has a different statement, so it cannot close the item. I retained the imported mathematical statement and dependencies, filled the current blueprint reference, recorded the required four Mathlib searches, and changed only the stage status and split metadata. The current main-20261015 blueprint proof is the same two arguments used here. No statement correction or source error was found.

## What could not be finished

No proof was written in Lean, as required for stage 1. The natural-language split is complete and ready for delivery.

## Review by Q35

I read the item source and proof in `literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-p-real-rankin/cor-rp-euler-product.md` and its `.proof.md`, as well as the imported master copy retained in the node. I also read the current Lean declaration and docstring in `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Rankin.lean` around lines 448–465. The Lean declaration is explicitly `by sorry` and has the polynomial-existence conclusion, so I did not attach it.

For step 1, I opened `thm-trf-l-function-euler-product.json`, `thm-trf-grothendieck-lefschetz-qbar.json`, and `def-weil-punctual-weights.json`. The first node states the Euler-product trace theorem and, in the dimension-at-most-one degree-zero sheaf case, the ratio with the three compactly supported cohomology determinants. Its hypotheses cover the separated finite-type curve and the finite-level trace-formula assumptions used here. The second node states the finite-level hypotheses and the Qbar Grothendieck–Lefschetz trace identity; I checked that the item applies it to the same lisse sheaf over `Qlb`, without changing coefficient categories. The punctual-weights definition supplies the local geometric Frobenius notation; identifying its degree `e_x` with the closed-point degree `d(x)` is the notation in the item. I checked the displayed local factor and the intermediate denominator with `H_c^0`, `H_c^1`, and `H_c^2` against these statements. The three quotations in `citations.json` are verbatim substrings of those node statements.

For step 2, I opened `lem-a1-affine-hc0.json`. Its statement has exactly the same smooth geometrically connected affine curve and lisse Weil sheaf hypotheses and concludes `H_c^0(U, F)=0`. Substituting this into the denominator from step 1 makes the degree-zero determinant equal to one and yields the item’s displayed fraction. The fourth quotation in `citations.json` is the complete verbatim statement of that node. This step is not marked elementary because it invokes the cited vanishing lemma.

I checked the item’s statement dependencies (`d-real-cohom`, `thm-trf-grothendieck-lefschetz-qbar`, and `def-wf-weil-category`) against every notion appearing in the statement, and the proof dependency union against the `uses` lists. No cited node is a definition being used as a theorem, no fact is taken from a cited proof rather than its statement, and no new node duplicates an existing DAG or blueprint node. I tested the edge cases conceptually: if the sheaf is zero, every local and cohomological determinant is one; the affine `H_c^0` vanishing removes exactly the stated factor; and the formula retains the `H_c^2` denominator. The Mathlib searches were run with the item id and recorded in the node; they returned only generic arithmetic Euler-product results and no declaration of this geometric Weil-sheaf statement.
