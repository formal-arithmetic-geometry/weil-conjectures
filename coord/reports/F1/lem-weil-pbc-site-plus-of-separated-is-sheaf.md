# Stage 1 Delivery Report

Item: `lem-weil-pbc-site-plus-of-separated-is-sheaf`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-site-plus-of-separated-is-sheaf.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-site-plus-injective-separated.json`
- `coord/reports/F1/lem-weil-pbc-site-plus-of-separated-is-sheaf.md`

## Change

The item is split along Stacks Sites Theorem 00WB(2). The first proof step delegates the injectivity clause to the new public unsplit node `lem-weil-pbc-site-plus-injective-separated`, which states the separated-presheaf injection and records the exact 00WA/00WB source. The existence step chooses local representatives of each compatible plus section using the existing public plus-presheaf node, compares their restrictions on every fibre-product overlap using injectivity, and glues the resulting family by the site transitivity axiom and the H^0 definition. The final step applies separatedness of the plus presheaf to obtain uniqueness.

No Lean was written or compiled. The new child node is statement-only, carries `created.item` equal to this item, and has independent LeanSearch, LeanFinder, Loogle, and Mathlib-source grep records. No existing node was modified.

## Review by F1

I checked the split against the actual proof of Sites Theorem 00WB(2), including the source's use of local representatives from Lemma 00W9 and the separatedness argument in the proof of item-sheaf. The new child node isolates the nontrivial injectivity fact, so the parent does not cite itself or hide a reusable lemma in a proof step. In the gluing step, each local plus section is represented on a cover of its base object; after pulling the assumed equality to a fibre product of two representative pieces, the child injectivity statement gives equality of the underlying presheaf sections. Site transitivity makes all representative pieces a cover of the original object, and the pairwise equalities are exactly the H^0 compatibility condition. The restriction formula for the plus presheaf then recovers each prescribed section, while the same injectivity/separatedness clause gives uniqueness. The statement and all dependencies remain on unit `sk-thm-p1`; no route departure or duplicate node was introduced.

## Validation

`python3 tools/review_split.py lem-weil-pbc-site-plus-of-separated-is-sheaf` and `python3 tools/check_dag.py --cycles` were run before delivery; `tools/preflight_delivery.py` is run after rebasing onto the current `origin/sheaf-dag` tip. No server merge tool or other server script was used.
