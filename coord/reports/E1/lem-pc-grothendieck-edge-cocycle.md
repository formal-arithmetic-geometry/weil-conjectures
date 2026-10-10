## Files written

- `dag/nodes/sec-picard-framework/lem-pc-grothendieck-edge-cocycle.json`: repaired item split.
- `dag/nodes/sec-picard-framework/lem-pc-grothendieck-ss-double-complex-model.json`: new statement-only node; no Mathlib match.
- `citations.json`: verbatim citation quotes for every step/node use.

## Attachments

None. The slopmaster2 grep still finds only the abstract `CategoryTheory.Functor.grothendieckLeftEdge` and `grothendieckLeftEdgeMap` definitions, not this cocycle theorem.

## WANTED

None.

## What was repaired

The returned split incorrectly claimed that `lem-sp-grothendieck-edge-maps` defined the abutment quotient, inclusion into `E_2`, and cocycle formula. Its statement only gives the two edge directions and functoriality. I added `lem-pc-grothendieck-ss-double-complex-model`, sourced to Derived Categories Lemma 015N proof, whose statement supplies the Cartan--Eilenberg double-complex realization, the `E_2` page, the abutment identification through `H^n(G(F(I^\\bullet)))`, and the precise edge-map comparison. The node is statement-only and does not repeat the cocycle formula.

Step 2 now explicitly compares the augmentation to the double complex, writes the finite-filtration edge as `H^n(Tot) -> F^0/F^1 = E_infinity^{0,n} -> E_2^{0,n}`, and computes on a cocycle that this is `G` applied to `Z^n -> H^n(F(I^\\bullet))`. Step 3 names the bigraded exact couple of that filtration and applies the collapse lemma there; it obtains the left edge identification from the new model node rather than from the abstract edge-map node. All three step sources now read `literature/stacks-project/derived.tex`, Lemma 015N proof, as required. The item's stale `created.item` was also corrected.

## Review by E1

I reread the statements of `lem-sp-grothendieck-edge-maps`, `thm-sp-grothendieck`, `thm-sp-if-e1`, `thm-sp-double-complex-spectral-sequences`, `def-sp-exact-couple`, `def-sp-convergence`, and `lem-sp-edge-collapse`. In particular, I verified that the old edge-map statement does not mention `E_infinity`, quotients, inclusions, or cocycles, while the new model statement does mention the filtered total complex, its `E_2` page, abutment, and edge comparison. For Step 1 I checked the injective-resolution and derived-functor statements. For Step 2 I checked the Cartan--Eilenberg and double-complex hypotheses, the acyclicity condition from the composable-pair statement, the left-exact kernel calculation, and the new node's exact edge sentence. For Step 3 I checked that the exact couple is explicitly the bigraded couple of the double-complex filtration, that its convergence and finite filtration are stated by the cited nodes, and that the collapse hypothesis is exactly vanishing outside the `p=0` column. Every entry in `citations.json` is a verbatim substring of its cited statement. I also searched the project Lean source and Mathlib for a theorem giving this model or cocycle formula; none exists. Degree zero and the identity-functor specialization remain consistent with the displayed map.

## What could not be finished

No unresolved split issue remains.
