# Worker report: lem-finrepair-modification-extension-zero

## Files written

- `dag/nodes/sec-smooth-purity/lem-finrepair-modification-extension-zero.json`: item marked `split`; retained the finite-ring statement and five-step proof, and refreshed the recorded Mathlib searches.
- `citations.json`: 18 verbatim statement quotations, one for each current step/node citation.
- No new nodes were created: every non-elementary input is already present in the shared DAG.

## Attachments

No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states the item or carries the blueprint tag. The matching declaration in the local new-target Lean packet is explicitly `by sorry`, so it is not an attachment. No Mathlib declaration gives the proper-modification etale assertion.

## WANTED

None. The cited Stacks source is present locally at `literature/stacks-project/` and the item follows Tags 03S6, 03S5, 03Q1, 0DDF, 04JN, 03PU and the cited derived-exchange statements.

## What was wrong or incomplete

The imported node was still `unsplit` despite already containing the complete expanded proof and review metadata. I changed only its stage-1 status and replaced stale imported search records with the eight searches actually run through `msearch.py` on 2026-10-17. The short master-blueprint proof omits the module-category exchange details; the item proof retains the expanded five-step route needed to identify the specified canonical adjunction map. No hypothesis or conclusion was corrected, and no proof dependency was removed. The current blueprint has the same lemma under its six-functors-basics snapshot; the item's existing blueprint identity remains the imported master node, with no distinct `same_as` formulation.

## What could not be finished

Nothing in the stage-1 split remains unfinished. No Lean files were written and no compiler, Lake, or build tool was run.

## Review by N5

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the complete delivery-errors B--E checklist, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, the fixed chapter `dag/chapters/sec-smooth-purity.json`, the unit `dag/units/sk-prop-sf-cbc.json`, both the master and main-20261015 blueprint records, and the item JSON. I also read the stage-2 reference declaration and docstring in `lean/Sheaf/AlgebraicGeometry/ModificationExtensionZero.lean`; its body is `sorry`, while the read-only slopmaster2 source has no declaration for this tag.

The item statement agrees with the master blueprint and the surrounding finrepair context: a finite commutative coefficient ring, a proper `π`, an open immersion `j`, the cartesian open `U'`, an isomorphism `h`, an arbitrary module sheaf `G`, the specified inverse-base-change adjunction map, and vanishing for every positive degree. I checked the edge cases used by the argument: outside `U` the extension stalks are zero; over `U` the fibre is the geometric point itself because `h` is an isomorphism; the assertions also make sense for the zero sheaf and for `q=1` (the first positive degree). No finite-stalk, constructibility, or coefficient-invertibility hypothesis was added.

Step 1 uses the exact statement of `lem-weil-pbc-etale-shriek-base-change-modules`: its cartesian square, etale `j`, module sheaf, and invertible base-change map give `j'_!h^{-1}G ≅ π^{-1}j_!G`. It uses `lem-weil-pbc-open-immersion-etale` for the required etale hypothesis, `def-weil-pbc-extension-by-zero` for the open-immersion sum having at most one lift, and `def-weil-pbc-inverse-image` for the unit and adjunction. The map `a` is explicitly the adjoint of the inverse base-change isomorphism; this fixes the canonical map whose stalks are checked later.

Step 2 uses `cor-weil-pbc-geometric-fiber-finite` with the proper morphism `π`, finite ring `Λ`, and bounded-below complex `F[0]`. Its statement gives exactly the exchange `\bar x^{-1}Rπ_*F ≅ Rr_*i^{-1}F`; no finite-stalk condition is present. The fibre notation and the fact that `F[0]` is bounded below are elementary.

Step 3 uses `lem-weil-pbc-extension-by-zero-stalks` at geometric points outside `U`, `lem-weil-pbc-inverse-image-stalk-germ` to identify inverse-image stalks, and `lemma-weil-pbc-geometric-stalk-conservative` on the map from the zero sheaf. These statements give zero stalks and hence `i^{-1}F=0`; the zero derived image and the zero stalk of `E` then follow. The point-set observation that a point of `U'` maps into `U` is elementary and is the only fibre-support inference in this step.

Step 4 is the long step, so I read each cited statement rather than treating its comparisons as implicit. The pullback universal property plus base change of the inverse of `h` identifies the fibre with `P`; this is the routine categorical calculation. `lem-weil-pbc-extension-by-zero-stalks` and `lem-weil-pbc-inverse-image-stalk-germ` give both stalk identifications, while `lem-weil-pbc-geometric-point-pullback-stalk` gives exact sections on `P` and identifies sections with the geometric stalk. `def-weil-pbc-direct-image` supplies the representative-section formula for the underived comparison. `lem-weil-pbc-exchange-forget-coefficients` says forgetting coefficients preserves the actual exchange morphism, and `lem-weil-pbc-derived-exchange-termwise` says the derived exchange is computed termwise on an injective resolution; together they identify its degree-zero map with `Ex^0_F`. The displayed germ compatibility from `lem-weil-pbc-inverse-image-stalk-germ` then shows that the specified adjunction map is the inverse of the stalk base-change identification. I checked that every use is of the cited node's statement, not of a construction hidden in its proof.

Step 5 uses `lem-weil-pbc-geometric-point-pullback-stalk` for exact stalk sections, `prop-weil-pbc-inverse-image-modules-exact` for exact inverse image on module sheaves, and `lemma-weil-pbc-geometric-stalk-conservative` for the final sheaf-level conclusions. Taking cohomology of the exchange from Step 2 gives the stalks of each `R^qπ_*F`; Steps 3--4 make the positive stalks zero and the degree-zero map invertible. Forgetting to abelian sheaves reflects zero objects and isomorphisms, so the conclusion is exactly the module-sheaf assertion.

All 18 citation entries copy the complete current statement of their node verbatim, so the citation checker can verify each quote directly. I searched the DAG for every dependency by id, Stacks tag, and key phrase before relying on it; no new node was needed and there is no new duplicate pair. I ran both original and second-phrasing LeanFinder, Loogle, LeanSearch and Mathlib-grep searches for the item. They returned only unrelated scheme-section or generic category results (or no hit), so the item is not a Mathlib leaf. The item is now a complete stage-1 split with its existing blueprint ancestry and no cycle.
