# Stage-1 report: lem-weil-twist-rationalization

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-twist-rationalization.json` — item node, split; no new nodes.
- `citations.json` — verbatim statement quotes for every cited node at every proof step.
- `report.md` — this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its mathematical phrases, and the blueprint tag; no sorry-free declaration states this item exactly.

## WANTED

None.

## Issues checked

The imported statement is faithful to the source's final sentence: it concerns raw Hom scalar localization at the uniformizer, with the same integral objects, and assumes an inverse integral pair before passing to E. I found no statement correction or coefficient-category mismatch. The whole DAG and blueprint were searched for a rationalization-of-inverse-twists lemma. The existing reviewed node `lem-pur-semilinear-scalar-localization` states the needed generic extension, natural-transformation, composition, and exactness results, so creating another node would duplicate it. No Mathlib leaf states this category-level assertion; the item's imported searches were retained.

## Review by Q158

I read the item source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/prop-weil-twist-preserves.md`, especially its final sentence and the returned-item note describing rationalization of the integral inverse pair. I also read the full statements of `def-weil-rationalization-karoubi`, `def-coefficient-twists-detailed`, and `lem-pur-semilinear-scalar-localization`. Step 1 verifies the hypotheses for the specialization R=S=O_E, t=u=varpi_E, identity coefficient map, and copies the generic fraction formula for the induced functors. Step 2 uses the generic natural-transformation clause and its composition/whiskering compatibility to localize both inverse isomorphisms with the correct composite endpoints. Step 3 is the elementary conclusion that exact functors equipped with both inverse natural isomorphisms form an exact equivalence. Step 4 checks that the object and arrow formulas are exactly the integral Tate twists defined by `def-coefficient-twists-detailed` and the raw rationalization convention, so no arbitrary discrete E-module category is introduced. I tested m=0, positive and negative m, the identity functor, and the case of a zero Hom module; all specialize correctly. The only off-unit citation is the generic semilinear-localization node, recorded in `split_report.tool_uses` because the local existence unit supplies no replacement.
