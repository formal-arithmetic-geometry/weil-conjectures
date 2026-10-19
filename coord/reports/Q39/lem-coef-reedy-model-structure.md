# Stage-1 delivery report: `lem-coef-reedy-model-structure`

## Files written

- `dag/nodes/sec-six-functors/lem-coef-reedy-model-structure.json` — statement; split proof retained and rechecked, with status set to `split` and the Q39 search handoff appended.
- `dag/nodes/sec-six-functors/lem-coef-small-direct-colimit-lifting.json` — supporting statement node; `unsplit` (no Mathlib match).
- `citations.json` — 16 step/node quote entries covering every citation in the item proof.
- `report.md` — this report.

## Attachments

None. I searched the named source checkout and the project source tree for the item id, its Reedy/model-structure declarations, and the recorded Lean declaration name. No exact sorry-free declaration was present.

## WANTED

- WANTED: Hovey, *Model Categories*, Remark 5.2.3 and Theorem 5.2.5, printed pp. 124–126, for `lem-coef-reedy-model-structure` (the PDF is cited online by the imported node but is not archived under `literature/`).
- WANTED: Hovey, *Model Categories*, Proposition 5.1.4 and Corollary 5.1.5, printed pp. 121–122, for `lem-coef-small-direct-colimit-lifting` (the PDF is not archived under `literature/`).

## Not duplicates

- `lem-coef-small-direct-colimit-lifting` vs `lem-coef-direct-wfs-extension`: the existing node assumes a finite direct category and proves a complete functor-category weak factorization system; this node allows any small degree-ordered category and proves only the left-lifting conclusion for its colimit map.
- `lem-coef-reedy-model-structure` vs `lem-coef-finite-reedy-localization`: the existing node is a finite-diagram localization/comparison result; this item constructs the Reedy model structure for arbitrary small Reedy categories and includes the latching/matching formulas and functorial factorizations.
- `lem-coef-reedy-model-structure` vs `lem-coef-reedy-colimit-comparison`: the existing node assumes the Reedy structure and proves a colimit preservation consequence; this item is the construction and verification of that structure.

## What was wrong or incomplete in the imported material

The imported item had a full proof but was still marked `unsplit`, and its citation ledger was absent from the Q39 sandbox. I changed only that status and supplied the required citation quotes and current search records. The finite direct WFS node is insufficient for the item’s arbitrary small latching slices, so the proof correctly uses the separate small-direct-colimit lifting node. No statement error or source error was found. The Hovey source is not available in the local literature tree, so both proof nodes retain `proof_origin.by = agent` and the WANTED entries above.

## What I could not finish

No Lean code or compilation was authorized at this stage. The natural-language split, citation ledger, duplicate audit, and Mathlib searches are complete; the delivery dry run is the remaining mechanical check.

## Review by Q39

I read the item JSON, the `sec-six-functors` chapter record, the `sk-prop-sf-biduality-general` unit record, the preserved supporting node, and the Hovey places named by their `source` fields. The item’s first three steps use only the colimit/limit universal properties; the quote for `def-weil-pbc-category-colimit` records that universal property verbatim. Steps 4–6 use the arbitrary-small direct-colimit node for latching slices and `lem-coef-lifting-class-closure` for identities, pushouts, composition, retracts, and the diagonal definition; the recorded quotes state each of those facts. Steps 7–10 use pointwise colimit/limit constructions, the opposite-category argument, and the same two closure statements; every non-elementary node use has a matching entry in `citations.json`. Step 11 uses the simplicial-set definition node for the category Δ and its order-preserving maps, then explicitly checks the unique surjection/injection image factorization, the opposite structure, empty and singleton cases.

I inspected the two proof steps exceeding 2000 characters. Step 2 is one degree-extension construction whose subclaims are the universal-property equations and the single inverse/direct functor-law check; Step 3 is one partial-factorization construction whose subclaims are the displayed pushout/pullback component equations. Neither hides an independent lemma with separate hypotheses, so no additional node is needed. I checked that every cited node says the fact used, that all uses occur in `proof_deps`, that arbitrary smallness and unbounded natural degrees are handled, and that the degree-zero and empty-category edge cases are stated. The Mathlib searches were rerun with the required Q39 command for both the item and the supporting node; they found only general model-category/Reedy indexing or transfinite-colimit declarations, so no Mathlib leaf was recorded.
