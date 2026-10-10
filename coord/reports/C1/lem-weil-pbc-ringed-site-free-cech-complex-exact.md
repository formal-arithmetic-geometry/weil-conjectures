# Delivery report

1. Files written: `dag/nodes/sec-curve-estimates/lem-weil-pbc-ringed-site-free-cech-complex-exact.json` (statement, split; no new nodes).
2. Attachments: no Lean declaration attaches to the item. The source search found no declaration carrying the item tag or the Stacks 03F5/03AT free-presheaf theorem.
3. WANTED: none.
4. What was wrong or incomplete: the imported item had an empty proof despite the statement being the general ringed-site version of the Stacks 03F5 argument. I supplied the decomposition and contracting-homotopy route. No statement was changed and no duplicate node was created; the existing `lem-weil-pbc-power-set-complex-contractible` node was searched and cited.
5. What could not be finished: no mathematical part remains unfinished.

## Review by C1

I read `literature/stacks-project/sites-cohomology.tex`, Lemma 03F5 (label `lemma-complex-tensored-still-exact`) and the underlying Lemma 03AT proof. The item statement matches the source: an arbitrary ringed site, a covering family with the required fibre products, free presheaves evaluated as sums over morphisms, and exactness only in positive degrees. I also read the cited definition nodes: `def-weil-pbc-sites-and-cohomology` supplies the site fibre products and presheaf category, and `def-weil-presheaf-modules-sheafification` supplies the objectwise free presheaf-module meaning.

Step 1 uses only those definitions and the elementary fact that presheaf exactness is objectwise; its displayed basis and alternating differential are the definition of the free presheaf and induced projections. Step 2 uses the site node's fibre-product universal property and checks that a morphism over a fixed $\\varphi:W\\to U$ is exactly a tuple of lifts, with face maps deleting entries. Step 3 uses the existing power-set node for the precise free-module-on-tuples complex and otherwise only the elementary direct-sum decomposition and objectwise homology calculation. Step 4 uses that node's two stated edge cases verbatim: an empty lift set gives the zero complex, while a nonempty lift set has $H_p=0$ for $p>0$ by the insertion homotopy. The hypotheses were checked for every object $W$ and every map $W\\to U$; no nonempty-lift assumption was silently imposed. I tested the one-index identity cover (each nonempty lift set gives the standard contractible complex), an empty lift set, and a zero coefficient ring.

The only non-elementary citation is the power-set complex, which comes from another unit and is declared in `split_report.tool_uses` because this unit has no replacement for that generic set-level lemma. Mathlib searches already recorded on the item found no site-level theorem, so no Mathlib leaf or new statement-only node was added.
