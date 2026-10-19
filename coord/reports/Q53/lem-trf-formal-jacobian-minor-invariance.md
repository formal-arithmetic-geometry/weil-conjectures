# Stage 1 report: lem-trf-formal-jacobian-minor-invariance

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-formal-jacobian-minor-invariance.json` — split item, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-formal-jacobian-coordinate-chain-rule.json` — new unsplit statement node, no Mathlib match.

## Attachments

None.

## WANTED

None.

## Not duplicates

- `lem-trf-formal-jacobian-coordinate-chain-rule` vs `lem-trf-formal-jacobian-minor-invariance`: the item asserts equality of the full Jacobian minor ideals under generator and coordinate choices; the helper only states the chain rule and invertibility of the coordinate-change Jacobian used in one proof step.
- `lem-trf-formal-jacobian-coordinate-chain-rule` vs `lem-weil-pbc-power-series-first-order-coordinates`: the existing node identifies the first-order quotient with a square-zero extension; the new node states the formal derivative chain rule and invertibility for a full regular-parameter coordinate change.
- `lem-trf-formal-jacobian-coordinate-chain-rule` vs `lem-weil-pbc-power-series-full-coordinates-cohen`: the existing node constructs coordinates over a Cohen ring; the new node is the field-valued chain-rule statement used in Tag 0C4B.

## Source and split

I read Stacks Project `literature/stacks-project/curves.tex`, Tag 0C4B (`lemma-fitting-ideal-well-defined`), including its statement and direct proof. The item keeps the hypotheses and fixed-size minor conventions exactly: a field, a formal power-series ring, a finitely generated ideal, any finite generating list, and any regular system of parameters. The source's generator calculation is expanded using the Cauchy–Binet statement already present in `lem-weil-pbc-cauchy-binet`. The coordinate paragraph's omitted details are isolated as `lem-trf-formal-jacobian-coordinate-chain-rule`; its statement records both the chain rule and invertibility needed for the reverse inclusion. Coordinate invariance then uses the existing clause `J_r(AC) ⊆ J_r(A)` in `lem-trf-fitting-ideal-minor-inclusions`.

## Review by Q53

I checked the item's source and every cited node. Step 1 handles `r=0` and all oversized or empty matrices directly from the item's conventions. Step 2 uses only the Cauchy–Binet formula stated by `lem-weil-pbc-cauchy-binet`: after reducing the derivative identity modulo `I`, each selected minor of the new generator Jacobian is a sum of old minors times coefficients; symmetry supplies equality. Step 3 takes exactly the chain-rule and invertibility assertions stated by the new coordinate node, then applies clause (3) of `lem-trf-fitting-ideal-minor-inclusions`; the inverse coordinate change gives the reverse containment. I verified that the cited statements provide the facts used and that `proof_deps` is the union of the step uses. I searched the DAG and blueprint for Tag 0C4B, chain-rule wording, and formal Jacobian minor invariance; no duplicate of the new helper statement was found. Small cases checked include `r=0`, `r` larger than the matrix dimensions, the zero ideal with redundant generators, and a one-variable nonlinear coordinate change such as `y=x+x^2`, whose derivative is a unit in `F[[x]]`.

## Corrections

The imported item had no proof steps. I added the missing Cauchy–Binet generator argument, made the source's coordinate calculation explicit through a separate statement node, and filled the blueprint and split-report metadata. No statement hypotheses or conclusions were changed.
