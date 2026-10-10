Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-ample-finite-principal-affine.json` — repaired 09NV proof.
- `dag/nodes/sec-curve-estimates/lem-sc-ample-finite-set-affine.json` — new unsplit 01ZY statement.
- `dag/nodes/sec-curve-estimates/lem-sc-graded-prime-avoidance.json` — new unsplit 00JS statement.
- `dag/nodes/sec-curve-estimates/lem-sc-closed-subset-qc-ideal.json` — corrected source tag and Mathlib candidate audit.
- `citations.json` — verbatim statement quotes for every cited step.

Attachments: none.

WANTED: none; the Stacks TeX sources were read from the available `c1-stacks-review` checkout, specifically `properties.tex` lines 5244–5330 and `algebra.tex` line 13630.

The returned finite-product argument was false: sections nonvanishing at separate points need not have a product nonvanishing at all of them. I replaced it with 09NV's own proof: 01ZY gives an affine open U containing E, the graded section ring and 00JS provide one homogeneous section s avoiding all point primes and vanishing on Y minus U, and 01PV makes Y_s affine. The empty-E case remains explicit. The closed-subset node now cites Schemes Lemma 01J3, and its Mathlib search records `Scheme.IdealSheafData.vanishingIdeal` and `coe_support_vanishingIdeal` as a candidate that does not state the required quasi-coherent-subsheaf theorem.

## Review by J1

I read the exact 09NV proof in `properties.tex`, including its first paragraph invoking 01ZY, its graded-ring construction and 00JS invocation, and its final 01PV conclusion. I also read 01ZY's proof and 00JS's statement in `properties.tex` and `algebra.tex`, and the 01J3 construction in `schemes.tex`. Step 1 cites the new 01ZY statement, whose hypotheses match the restriction of the ample invertible sheaf to W. Step 2 cites the existing ample ideal section statement for the noncontainment of I in each point prime and the new graded prime avoidance statement for the simultaneous homogeneous section. Step 3 cites the existing affine-cap-section statement and checks E subset Y_s subset U; the zero section handles E empty. I checked every citation quote against the cited node statement in `citations.json`, verified positive degree and affine hypotheses, and removed the invalid product construction. Mathlib searches were recorded for both new nodes and the corrected closed-subset node.
