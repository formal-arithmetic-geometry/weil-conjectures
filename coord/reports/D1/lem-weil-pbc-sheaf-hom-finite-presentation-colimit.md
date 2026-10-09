## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sheaf-hom-finite-presentation-colimit.json`: repaired parent proof citation and added the local-isomorphism child dependency; parent follows Modules 0GMV with exact tags 01AH(2),(3), 01CO, and Sheaves 00WY.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ringed-space-colimit-restriction.json`: `lem-weil-pbc-ringed-space-colimit-restriction`, statement, Mathlib verdict no exact generic match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sheaf-hom-finite-presentation-kernel.json`: `lem-weil-pbc-sheaf-hom-finite-presentation-kernel`, statement, Mathlib verdict no exact module-valued sheaf-Hom match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sheaf-isomorphism-local-open-cover.json`: `lem-weil-pbc-sheaf-isomorphism-local-open-cover`, statement, Mathlib verdict generic sheaf cover criterion only.

## Attachments

None.

## WANTED

None. The relevant Stacks tags are cited from the obtained literature references.

## Problems found and repaired

The returned delivery's two child statements used plain text notation and omitted object dependencies and exact Stacks tags. The restriction node now introduces the open immersion, restricted sheaves, module category, colimit, and sheafification in TeX and cites Modules 01AH(2),(3) and Sheaves 009E. The Hom-kernel node now states the exact sequence with `\\mathcal Hom`, finite direct sums, and module-sheaf dependencies and cites Modules 01CO(1),(2). Its unrelated local-isomorphism clause was split into `lem-weil-pbc-sheaf-isomorphism-local-open-cover`, citing Sheaves 00WY; the parent proof uses this node explicitly.

## Checks

- `python3 tools/check_dag.py`: passes; seven pre-existing reachability warnings remain.
- `python3 tools/review_split.py lem-weil-pbc-sheaf-hom-finite-presentation-colimit`: PASS; all three new nodes have searches and verdicts.

## Could not finish

Nothing remains for this item beyond lead review.

## Review by D1

I checked the split directly against Modules 0GMV, 01CO, 01AH and Sheaves 009E/00WY. During review I rejected the first Hom-kernel child because it reversed the variance of internal Hom; the worker corrected it to the contravariant exact sequence and I rechecked the result. The three reusable child nodes have explicit object dependencies, exact source tags, and all required Mathlib search kinds. `review_split.py` passes and the new proof dependencies match the steps.
