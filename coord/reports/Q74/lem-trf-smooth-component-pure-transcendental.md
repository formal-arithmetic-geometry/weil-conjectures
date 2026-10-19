## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-component-pure-transcendental.json`: statement split into four proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-connected-point-geometrically-connected.json`: statement-only intermediate fact; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-smooth-geometrically-normal.json`: statement-only intermediate fact; no Mathlib match.

## Attachments

None. I searched the slopmaster2 source for the item id, blueprint tag, and the relevant geometric phrases; no sorry-free declaration states this item.

## WANTED

None. All cited source files are present in the local Stacks literature.

## What was checked and corrected

The imported item had the Tag 052E statement but no proof. I retained its hypotheses and conclusion. The source argument uses four separate facts, so I created one statement-only node for each fact after searching the whole DAG and blueprint for duplicates and searching Mathlib with LeanFinder, Loogle, grep, and LeanSearch. The searches found only general topology or integral-scheme declarations, not any of these Stacks results. The new nodes are strictly smaller than the item and do not restate its conclusion.

## Review by Q74

I read `literature/stacks-project/more-morphisms.tex` at Tag 052E and its proof paragraph beginning “Let T be the connected component”, together with `varieties.tex` Tag 04KV, `varieties.tex` Tag 056T, `properties.tex` Tag 033M, and the topology component-openness tags 04ME/04MF. Step 1 uses the existing Noetherian connected-components statement exactly for openness; finite type over a field gives Noetherianity, and Noetherian compactness gives quasi-compactness of T. Step 2 uses exactly the new 04KV statement: the purely transcendental residue field has k algebraically closed in it, while T is connected and contains c. Step 3 uses exactly the new smooth-geometrically-normal statement; restriction of smoothness to the open T is the local-definition observation used in Tag 052E. Step 4 uses the connectedness and geometric-normality statements from steps 2 and 3 after arbitrary field extension, plus exactly the existing `rem-pc-regular-normal` statement, yielding an integral T_K for every K/k. I checked the hypotheses at each use: finite type and smoothness are hypotheses of the item, c lies in T by construction, and purely transcendental means k is algebraically closed in the residue field. I tested the component conclusion on A^1_k, Spec(k(u)) as a point of A^1_k, a disconnected finite disjoint union of smooth components, and the empty scheme edge case (the item has a point, so T is nonempty). No statement was weakened or changed, no duplicate node was found, and no Lean file was written or compiled.

## Not duplicates

- `lem-trf-connected-point-geometrically-connected` vs `lem-sbc-connected-rational-point-geometrically-connected`: the existing node assumes a k-rational point, while this node uses the strictly more general condition that k is algebraically closed in the residue field.
- `lem-trf-smooth-geometrically-normal` vs `lem-sbc-smooth-section-component-geometrically-irreducible`: the existing node constructs a fibrewise component neighbourhood with a section; this node states smooth-over-a-field geometric normality.

- `lem-trf-connected-point-geometrically-connected` vs `lem-sbc-connected-rational-point-geometrically-connected`: the existing node assumes a k-rational point, while the new node uses the strictly more general condition that k is algebraically closed in the residue field.
- `lem-trf-smooth-geometrically-normal` vs `lem-sbc-smooth-section-component-geometrically-irreducible`: the existing node constructs a fibrewise component neighbourhood with a section; the new node states smooth-over-a-field geometric normality.
- `lem-trf-connected-point-geometrically-connected` vs `lem-sc-av-commutative`: the existing 04KV citation occurs inside a much stronger commutativity theorem and does not state the general geometric-connectedness criterion.
- `lem-trf-connected-point-geometrically-connected` vs `lem-sc-mult-n-finite-kernel`: the existing node concerns finite-kernel multiplication on an abelian variety and does not state the criterion.
- `lem-trf-connected-point-geometrically-connected` vs `lem-dl-a1-constant-field-charts`: the existing node uses 04KV in a constant-field chart construction; it does not state the general criterion.
- `lem-trf-connected-point-geometrically-connected` vs `lem-sbc-generic-pointed-clopen-fibres`: the existing statement assumes a rational section and a clopen fibre trace, while this node gives the residue-field criterion for any connected scheme.
- `lem-trf-connected-point-geometrically-connected` vs `lem-sbc-smooth-section-component-geometrically-irreducible`: the existing statement assumes a smooth family with section and concludes an open family property; this node is the standalone 04KV criterion.
- `lem-trf-connected-point-geometrically-connected` vs `new-lem-sbc-generic-pointed-clopen-fibres-core`: the existing core is a pointed-family spreading result; this node is the general connected-scheme geometric-connectedness criterion.
- `lem-trf-smooth-geometrically-normal` vs `lem-sc-hilb-geometrically-integral`: the existing Hilbert-scheme statement assumes a smooth proper geometrically irreducible curve and does not state smooth geometric normality.
- `lem-trf-smooth-geometrically-normal` vs `lem-sc-smooth-algebra-reduced-field`: the existing statement is the affine algebra smooth-implies-reduced result, with no scheme geometric-normal conclusion.
- `lem-trf-smooth-geometrically-normal` vs `lem-sbc-finite-etale-generic-fibre-hom-extension-existence`: the existing node is an extension theorem for finite étale covers over a generic fibre and only cites 056T as an input.
- `lem-trf-smooth-geometrically-normal` vs `lem-sbc-smooth-connected-generic-geometry-core`: the existing node assumes an integral base and geometrically connected fibres and concludes integrality of the total space; it is not the field-smooth geometric-normal theorem.
- `lem-trf-smooth-geometrically-normal` vs `lem-sbc-smooth-connected-generic-geometry`: the existing node is a generic-fibre integrality and function-field comparison result under stronger hypotheses.
- `lem-trf-smooth-geometrically-normal` vs `sbc-lem-smooth-geometrically-reduced`: the existing statement concludes geometrically reduced fibres of a smooth morphism, whereas this node supplies geometric normality of a scheme smooth over a field.
- `lem-trf-connected-point-geometrically-connected` vs `lem-trf-smooth-component-pure-transcendental`: the item is the full smooth-component conclusion including openness, quasi-compactness, and geometric integrality; this node isolates only the connected-point-to-geometric-connectedness implication.
- `lem-trf-smooth-geometrically-normal` vs `lem-trf-smooth-component-pure-transcendental`: the item concerns a connected component of a finite-type smooth scheme at a specified point; this node isolates smooth-over-a-field geometric normality.
