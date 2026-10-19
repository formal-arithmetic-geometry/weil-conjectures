# Stage-1 report: lem-trf-composite-fibre-dimension-inequality

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-composite-fibre-dimension-inequality.json`: split item; Mathlib searches found no matching declaration.
- `dag/nodes/sec-trace-formula/lem-trf-local-fibre-ring-dimension-inequality.json`: new statement-only node for Stacks Tag 00OM; Mathlib searches found no exact match.
- `citations.json`: verbatim statements for every citation used by every proof step.
- `searches.jsonl`: the five required recorded Mathlib searches.

## Attachments

No sorry-free declaration in the slopmaster2 source states this item. The source search found no declaration tagged `(blueprint: lem-trf-composite-fibre-dimension-inequality)` and no declaration with the exact 02JS conclusion.

## WANTED

None. The Stacks source and all cited DAG statements are present locally.

## Review by NL

I read the item node, the `sk-i-curve-zero` unit record, the `sec-trace-formula` chapter record, and Stacks `morphisms.tex` at Tag 02JS (including its proof) and Tag 02FX, together with Algebra Tag 02IJ. The statement is unchanged: it has exactly the two locally-finite-type hypotheses and the pointwise inequality, with no flatness assumption.

Step 1 checks the fibre objects against `def-pc-scheme-fibre`, uses the affine tensor-product identification, and verifies local Noetherianity from the finite-type maps to residue-field spectra. Step 2 applies the existing finite-type dimension formula to each of the three fibres and uses the open-subspace invariance statement to identify affine-chart and whole-fibre local dimensions. Step 3 follows 02JS exactly: the existing composite-fibre-local-model node identifies the Noetherian local rings and the closed fibre quotient, and the new Tag 00OM node gives the required local-ring dimension inequality without flatness. Step 4 uses the residue-field tower statement and explicitly regroups the three local-ring-plus-transcendence-degree formulas into the claimed inequality. No flatness or unproved equality is used, and empty fibres are harmless.

I searched the full DAG and blueprint for 02JS, 00OM, the dimension-formula labels, and the key phrases; the existing flat equality node is insufficient for this non-flat inequality, so the 00OM statement-only node was added. I also checked small cases: identity maps give equality, a closed immersion can give strict inequality, and a map to a point reduces to the ordinary local dimension bound. No statement correction or new node was needed.

## What was wrong or incomplete before this split

The imported node had no proof, proof dependencies, or Mathlib-search records suitable for this worker. I supplied the complete four-step natural-language proof and exact citations. The Mathlib search results were generic composition/smoothness or order-dimension declarations and did not match this scheme-fibre inequality.

## What remains unfinished

Nothing in this stage-1 item; the proof depends on existing DAG nodes that remain independently queued where applicable.

## Not duplicates

lem-trf-local-fibre-ring-dimension-inequality vs lem-weil-pbc-serre-sk-goes-up: the new node states the standalone Tag 00OM dimension inequality for every homomorphism of Noetherian rings, while the existing node states Serre condition $(S_k)$ ascent under flatness and only cites 00OM in its proof; it does not state the dimension inequality.
