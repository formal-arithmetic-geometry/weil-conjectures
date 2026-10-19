# Worker report

Item: `lem-coef-infinity-right-anodyne-saturation`; group Q68; 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-right-anodyne-saturation.json` — statement split into ten proof steps; no new nodes.
- `citations.json` — verbatim citations for every node used by every step.

## Attachments

None. The item was unsplit in the shared DAG and has no exact sorry-free declaration in the permitted source checkouts.

## WANTED:

WANTED: an archival copy of Kerodon Proposition 4.2.5.3 (tag 0153), including the proof of the two weak-saturation assertions; the online source is cited in the node because it is not present under `literature/`.

## What was wrong in the prior attempt

The prior attempt was blocked because the dispatcher snapshot did not yet contain the assigned node. The node is now present at the committed path, so I copied it and completed the split. The theorem is a genuine two-variable closure statement; I did not create clause nodes that would merely restate it. The existing neighbouring `lem-coef-infinity-right-anodyne-product` uses this item as a dependency, while the existing boundary-cell and prism nodes are inputs to that neighbouring theorem rather than facts needed for this closure lemma itself.

## Review by Q68

I read the copied item, its blueprint ancestry (`prop-coef-integral-exceptional-adjoint`), the unit record `sk-prop-sf-biduality-general`, the neighbouring Cartesian product node, and the Kerodon Proposition 4.2.5.3 proof route. The item statement is unchanged: it quantifies over an arbitrary weakly saturated class of simplicial maps, and for each fixed monomorphism in either variable asserts weak saturation of the corresponding Cartesian pushout-product preimage. Every hypothesis (small simplicial sets, degreewise monomorphisms, the displayed pushout, and the exact isomorphism/pushout/transfinite/retract closure conditions) is retained.

The ten steps first identify the pushout-product degreewise as the union `(A × L) ∪ (B × K)` and establish functoriality and retract maps. Steps 2–6 fix `k`: the isomorphism, pushout, continuous ordinal-chain, and retract clauses are checked in that order, with the limit-stage union written explicitly. Steps 7–10 repeat the same four checks with `i` fixed. The only cited definitions are `def-cbc-enhanced-diagrams-cones`, whose statement supplies degreewise simplicial products and operators, and `def-weil-pbc-category-colimit`, whose statement supplies the colimit/pushout universal construction; `citations.json` quotes the exact sentences used. The closure properties of `W` are hypotheses from the item itself, so no separate node was invented for a clause of the item.

I searched the whole DAG and blueprint for the statement and for existing weak-saturation/pushout-product lemmas. The only nearby theorem is the already split `lem-coef-infinity-right-anodyne-product`, which uses this item; it does not state the arbitrary-class closure theorem. The Mathlib searches recorded in the node were run for this Q68 item with LeanFinder, Loogle, grep, and LeanSearch; generic pushout and transfinite infrastructure was found, but no one-line theorem gives the stated right-anodyne/general weak-saturation result. Small edge cases were checked in the proof text: an isomorphism gives an isomorphism `θ`, and the zero-length ordinal chain is exactly that case; degree zero is covered because all arguments are degreewise and no nonempty simplex assumption is made. I corrected the stale blocked report by using the now-present node and removed two unnecessary citations that referred only to the item's own closure hypothesis.

## Not duplicates

`lem-coef-infinity-right-anodyne-saturation` vs `lem-coef-infinity-pushout-join-saturation`: the existing node concerns the join operation and inner-anodyne maps, whereas this item concerns Cartesian products and an arbitrary weakly saturated class.

`lem-coef-infinity-right-anodyne-saturation` vs `lem-coef-infinity-right-anodyne-product`: the existing node proves the right-anodyne Cartesian product theorem and cites this saturation lemma; it does not state closure of the preimage class for arbitrary `W`.

## Second reading by Q68

I reread Kerodon Proposition 4.2.5.3 (tag 0153) at the online source and checked the item statement hypothesis by hypothesis: both inputs are small simplicial sets, both maps are degreewise monomorphisms, `W` has exactly isomorphism, pushout, small transfinite-composition, and map-retract closure, and both fixed-variable conclusions are retained; the empty simplicial set and degree-zero cases are included.

- Step 1: checked against the degreewise product and pushout definitions in `def-cbc-enhanced-diagrams-cones` and `def-weil-pbc-category-colimit`; the union/intersection, simplicial-operator, and functorial/retract claims are explicit and pass.
- Step 2: checked against the isomorphism clause of tag 0153; the pushout-product of an isomorphism is an isomorphism, including the zero-length case, and passes.
- Step 3: checked against the pushout clause of tag 0153; the repaired square is explicitly the degreewise pushout, including arbitrary (possibly noninjective) attaching maps, and passes.
- Step 4: checked against the successor-stage argument of tag 0153; the repaired text explains why an ordinal chain of degreewise injections embeds in its colimit, then gives the successor pushout square, and passes.
- Step 5: checked against the limit-stage and transfinite-composition clauses of tag 0153; continuity is written as a degreewise union and the endpoint map is identified, so the closure inference passes.
- Step 6: checked against the retract clause of tag 0153 and Step 1's functoriality; the section/retraction squares induce the required map retract, and passes.
- Step 7: checked against the symmetric isomorphism argument in tag 0153; it has the same degreewise justification and passes.
- Step 8: checked against the symmetric pushout argument in tag 0153; the repaired text names both pushout-product domains and their intersection, so the pushout inference passes.
- Step 9: checked against the symmetric successor and limit argument in tag 0153; the colimit embedding, successor pushouts, and limit unions are stated explicitly, and passes.
- Step 10: checked against the symmetric retract clause in tag 0153; Step 1 supplies the induced retract and `W` supplies closure, so it passes.
- New nodes: none; there were no new-node statements to audit, and the two cited existing definition nodes say exactly the product/operator and colimit facts used.

Changes made in this second reading: clarified both pushout squares with their four maps and intersections; explained the degreewise embedding of an injective ordinal chain into its colimit in Steps 4 and 9; retained the original statement, source, dependencies, and search records. No statement correction or source error was found.
