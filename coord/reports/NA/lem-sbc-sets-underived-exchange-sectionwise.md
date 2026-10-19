# Worker report

## Files written

- `dag/nodes/sec-smooth-base-change/lem-sbc-sets-underived-exchange-sectionwise.json`: item split into five proof steps; no new nodes.
- `citations.json`: verbatim statement quotations for every node used by every step.

## Attachments

None. The item has no sorry-free declaration in the read-only source checkout.

## WANTED:

None.

## What was wrong in the imported item

The mathematical statement is the intended sheaf-of-sets formula, but its imported citations `[def-weil-pbc-inverse-image]` and `[def-weil-pbc-direct-image]` are the abelian-sheaf definitions. I replaced those citations in the statement and dependencies with the existing set-valued node `lem-weil-pbc-sets-etale-inverse-image-composition-units`, whose statement supplies the sheafification construction, the set-valued adjunction, units, and direct-image sections. No hypothesis or conclusion was changed. The imported node had no proof; the five steps now make the representative construction, transition compatibility, sheafification, adjunct calculation, and mate identification explicit. No duplicate or new lemma node was needed.

## Not duplicates

- `lem-sbc-sets-underived-exchange-sectionwise` vs `lem-weil-pbc-underived-exchange-sectionwise`: the former is the set-valued section formula for an arbitrary Cartesian square, while the latter is an abelian-sheaf well-definedness statement with a different presheaf construction and coefficient category.

## What could not be finished

Nothing; the stage-1 split and its citation file are complete. The required Mathlib searches were rerun for the item on 2026-10-18: LeanFinder (no match), Loogle (unavailable/unknown identifier), grep (no match), and LeanSearch (no match).

## Review by NA

I read the item source at Stacks Project `etale-cohomology.tex`, Tag 0EZR, including the proof of `lemma-base-change-local`, and the current blueprint paragraph `sbc-lem-etale-locality` that this item serves. I also opened the full statements of `def-weil-pbc-cartesian-square`, `def-pc-fibre-product`, `def-weil-pbc-etale-site`, `def-weil-pbc-etale-sheaf-of-sets`, `def-weil-pbc-sheafification`, and `lem-weil-pbc-sets-etale-inverse-image-composition-units`. The latter is the set-valued adjunction and direct-image source; the abelian-only inverse/direct-image nodes do not state what this item uses, so I removed them from the item dependencies.

Step 1 uses the set-valued inverse-image colimit and direct-image section formula, the small etale-site objects, and the fibre-product universal property to obtain exactly the triples `(W,a,s)` and the induced `ell_a`. Step 2 uses the unit-compatibility clause of the set composition node and functorial fibre products to verify both transition relations, including restriction in `V`; every cited statement says the unit restriction and fibre-product functoriality used. Step 3 uses the sheafification universal property to extend the presheaf map uniquely and uses the set node's naturality clause for naturality in `F`; this is where representative independence is proved. Step 4 evaluates the resulting adjunct on the identity representative and checks that it is the canonical fibre-product comparison map on sections. Step 5 uses the cartesian-square comparison `theta_square`, the set composition node's unit-compatible composition isomorphisms, naturality of the unit, and the adjunction triangle identity to identify that adjunct with `g'^{-1} epsilon_f` composed with `theta_square`; injectivity of the adjunction bijection then gives the defined exchange morphism. The small cases identity square, empty `V`, and the zero/terminal sheaf all reduce to the same representative formula, so no edge hypothesis was silently added.
