# Stage-1 report: lem-sfb-space-module-flattening-by-admissible-blowup

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-module-flattening-by-admissible-blowup.json`: split statement, seven proof steps, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-etale-ideal-factor.json`: new statement-only Tag 087B input, no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None. I searched the project Lean source for the item id, its title, and the relevant flattening names; no project declaration states this item.

## WANTED:

None. The source `literature/stacks-project/spaces-more-morphisms.tex` and the scheme flattening source `literature/stacks-project/flat.tex` are present.

## Not duplicates

- `lem-sfb-space-module-flattening-by-admissible-blowup` vs `lem-sfb-space-flattening-by-admissible-blowup`: the former is the module theorem for an algebraic space and explicitly defines etale-site module flatness and torsion strict transforms; the latter is the separate algebraic-space morphism/space strict-transform theorem.
- `lem-sfb-space-etale-ideal-factor` vs `lem-trf-etale-ideal-local-factor`: the new node is the global algebraic-space Tag 087B factorization for a quasi-compact separated etale morphism, while the existing node is only a local affine ring factorization at a prime with a nonzerodivisor on the base.
- `lem-sfb-space-etale-ideal-factor` vs `lem-trf-etale-chart-ideal-lift`: the new node produces a base ideal and a global product identity on spaces; the existing node only constructs a standard-etale chart and numerator generators.

## Source or statement checks

The item matches Tag 087C hypothesis by hypothesis: the base is qcqs, the open is quasi-compact, the space is quasi-compact and locally of finite presentation over the base, the module is finite type, and its restriction is finite presentation and flat. I retained the item statement and its existing statement dependencies. The new node is Tag 087B, with no surjectivity, Noetherian, or density hypothesis added.

## Review by Q07

I read Tag 087C in `literature/stacks-project/spaces-more-morphisms.tex` and the complete scheme proof of Tag 0815 in `literature/stacks-project/flat.tex`. I also read Tag 087B (the new ideal-factor statement), Tag 0863 and 0862 for etale-local module strict transforms, Tag 0868/080I for composition of transforms, and Tag 0814 for the scheme etale-local flattening route. The item’s seven steps follow that route: choose affine etale charts; verify qcqs, local finite presentation, finite type/presentation, and flatness; apply the scheme flattening theorem; use 087B to push down the centre; identify the flat base change with the product-centre blowup; use the existing scheme product-transform lemma; then descend finite presentation and flatness through the surjective etale charts.

For each step I opened every cited node and checked that its statement supplies the exact fact used. In particular, the affine-atlas node supplies an affine surjective etale atlas; the affine-source node supplies quasi-compactness and separatedness of the base chart; the fibre-product node supplies scheme charts and preservation of surjective etale covers; the qcqs product and scheme permanence nodes supply qcqs and quasi-compactness; the scheme etale/Zariski equivalence supplies the module identification and its finite-type/presentation transfer; the scheme flattening node supplies the first flat strict transform; the new 087B node supplies `J|_U = O_U` and `J O_W = I I'`; the blowup chart node supplies flat base change; the product-transform node supplies successive-transform equality and flatness after the second blowup; and the space transform-locality and arbitrary-chart flatness nodes supply the final descent.

I verified the hypotheses at their use sites: the affine base chart is qcqs, the open pullback is quasi-compact, the etale chart maps are flat and locally of finite presentation, the product centre is unit over the open, and the source chart covers every point after base change. I explicitly checked the torsion definition against localization at an exceptional equation and cited the locally-principal supported-kernel result. I tested empty centres, the unit ideal, the zero module, and an empty source chart. I corrected the new node to include the open-immersion dependency and repaired its citation quote; no statement or source hypothesis was silently weakened.

The item uses generic scheme/module and blowup lemmas from the trace-formula unit as declared `tool_uses`; none replaces the algebraic-space flattening route. All steps are below the long-step threshold. Mathlib searches were run with `msearch.py` and recorded in `searches.jsonl`; the returned declarations were inspected and none states either the item or the 087B factorization.
