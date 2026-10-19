# Worker report: lem-pur-cfiber-stalk

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-cfiber-stalk.json`: item split; no new nodes; no Mathlib leaf.
- `citations.json`: verbatim statement quotes for every cited proof step.
- `report.md`: this report.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint id and for compact-support, stalk, and geometric-fiber declarations; no sorry-free declaration states this item exactly.

## WANTED

None.

## Duplicate check

No new nodes were created. I searched the DAG for the item id, its title, and the compact-support/stalk/geometric-fiber phrases. The only occurrences are the item itself and its two downstream citers; no existing node states the same comparison.

## Statement and source audit

The item statement is unchanged from the current main-20261015 and imported master blueprint records. The chapter and unit records were read. The proof source is the main-20261015 proof paragraph, with the imported master paragraph checked against it. The main source has one compressed paragraph; I expanded it by coefficient stage while retaining its compactification and proper-base-change route. The generic coefficient notation is interpreted using the coefficient transports explicitly fixed by `def-pur-conventions`; finite coefficients are the base case and the integral, rational, and common-stage cases are transported through the corresponding compact-support constructions.

## Review by NK

I read the item, `sec-smooth-purity.json`, `sk-prop-an.json`, both blueprint versions of the item, and every statement cited by the five proof steps. Step 1 uses the compactification data from `def-compact-support-direct-image-detailed`, the filtered-neighborhood stalk definition from `def-weil-pbc-geometric-stalks`, and the inverse-image/stalk germ comparison from `lem-weil-pbc-inverse-image-stalk-germ`; these statements supply exactly the compactification, stalk, and inverse-image identifications used there. Step 2 checks the finite-level hypotheses by `lem-sf-proetale-constructible-origin`, then uses the actual pro-etale compact-support exchange of `thm-cbc-finite-level-proetale`; the proper factor is identified by the displayed geometric-fiber isomorphism of `cor-weil-pbc-geometric-fiber-finite`, and the retained witness is exactly the pair required by `def-weil-pbc-etale-origin-witness`. Step 3 uses the completed extension-by-zero reduction comparison, the completed exchange realization as a derived limit, and the explicit inverse-limit definition of integral compact support. The only extra inference there is functoriality of a derived functor on an isomorphism of strict towers. Step 4 uses the rational finite-extension exchange and the common-stage Qbar descent exactly as stated in `thm-cbc-finite-extension` and `thm-cbc-qbar`, with the integral/rational/common-stage definitions from `def-weil-integral-rational-qbar-compact-support`. Step 5 checks that all maps are canonical and natural under the cited comparison statements and records empty, zero, identity, and point cases.

I checked hypotheses at each stage: `pi` is separated finite type, the chosen compactification base changes along the arbitrary geometric point, finite-level objects have bounded etale-origin witnesses, completed objects have the required reduction towers, and rational/Qbar objects are represented at the stages required by their exchange theorems. I also checked small cases directly: empty `E`, `K=0`, `pi=id`, `B=Spec Omega`, and a geometric fibre with no points. No statement was weakened, no second definition was introduced, and no SGA 4 or SGA 4½ source was cited.

## Mathlib searches

The required LeanFinder, LeanSearch, Loogle, and Mathlib grep searches were run twice with distinct phrasings and recorded in `searches.jsonl`; they found only generic stalk/fiber and pushforward declarations, with no compact-support geometric-fiber theorem. The Loogle query containing `proper` initially returned an unknown-identifier diagnostic and the second Loogle query for `CategoryTheory.GrothendieckTopology.Point.sheafFiber` returned the generic fiber functor declarations; both outcomes are recorded verbatim in the item’s search records.

## What could not be finished

Nothing. No Lean files were written and no compiler or build tool was run, per the stage-1 instruction.
