# Worker report

- Files written: `dag/nodes/sec-six-functors/lem-coef-inert-relative-tuple-cone.json` (statement, split, no new nodes or Mathlib leaves), `citations.json`.
- Attachments: none; no declaration tagged `(blueprint: lem-coef-inert-relative-tuple-cone)` was found in either read-only source checkout.
- WANTED: Gepner–Haugseng, *Enriched infinity-categories via non-symmetric infinity-operads*, archival copy for Definition 3.1.3, Remark 3.1.4 and Proposition 3.4.5, pp. 602–603 and 615–616. The cited PDF was read online.
- The imported node was unsplit and had no proof. I retained its statement, dependencies, blueprint ancestry and external source, corrected the worker metadata to Q127, and supplied a four-step proof. No Mathlib declaration states this quasicategorical result; all six required searches were run and recorded in the node.

## Not duplicates

`lem-coef-inert-relative-tuple-cone` vs `lem-coef-inert-color-coslice-components`: the existing node decomposes a color coslice after cocartesian lifts have already been chosen; it does not construct a cone with prescribed boundary objects or characterize relative limits.

`lem-coef-inert-relative-tuple-cone` vs `lem-coef-infinity-relative-cone-equivalence`: the existing node gives invariance and the dual final-edge criterion for arbitrary relative cones; it does not use the monoidal Segal condition to construct the tuple cone.

## Review by Q127

I read the item, the unit `sk-prop-sf-biduality-general`, the chapter record, the blueprint proof paragraph, and the full statements of `def-coef-monoidal-infinity-category`, `def-coef-infinity-fibrations`, `lem-coef-cocartesian-joyal-fibration`, `def-coef-infinity-relative-cone`, and `lem-coef-infinity-relative-cone-equivalence`. Step 1 uses exactly the Segal equivalence, cocartesian lifts over the specified inert maps, and the Joyal lifting property to rectify the equivalent boundary to the prescribed boundary; the base map remains exactly `g`. Step 2 uses the monoidal definition's mapping-space product and matches it to the relative-limit mapping-square definition. Step 3 restricts to each singleton boundary and applies the cited node's explicit dual of its final-edge criterion, so every apex-to-color edge is cocartesian. Step 4 checks the zero-factor Segal product and empty mapping-space product, including the empty cone.

I checked the hypotheses point by point: the index is a discrete simplicial set, the base edges are precisely the inert projections `rho_i`, the fibration is cocartesian, and no ordinary limits, colimits, presentability, or extra coefficient assumptions enter. I tested n=0, n=1 (identity inert edge), n=2, the identity fibration, and a terminal fiber. The Mathlib searches returned only ordinary category-theory and strict Segal simplicial-set declarations, so this remains a non-Mathlib statement. The only correction was metadata and the addition of the complete proof; no new node was created because each dependency already exists and none restates the item.
