Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-open-curve-etale-leray-low-degree.json` (statement, split)
- `citations.json`

Attachments: none. No new nodes or Mathlib leaves.

The source checkout contains no declaration tagged for this item and no sorry-free declaration stating its full isomorphism. The project declaration `AlgebraicGeometry.Etale.injective_edgeMap_one` only proves injectivity in degree one. The first dry run rejected a proposed étale spectral-sequence child as too close to the item; I removed it and used existing generic DAG nodes.

## Not duplicates

No new nodes. The existing `thm-sp-grothendieck` and `lem-sp-grothendieck-edge-maps` are cited as generic tools.

## Review by J1

I checked the item's statement against its parent `lem-sc-open-curve-gm-direct-image-cohomology`, whose second step needs precisely the low-degree Leray comparison. Step 1 uses `lemma-weil-pbc-geometric-stalk-conservative`: applying its exact isomorphism criterion to the map from each higher direct-image sheaf to zero converts both stalk hypotheses into sheaf vanishings. Step 2 uses `lem-weil-pbc-direct-image-preserves-injectives` for the acyclicity condition of `thm-sp-grothendieck`; both statements explicitly cover abelian étale sheaves. The definition of cohomology and direct image identifies the derived global sections of the composite, and `lem-sp-grothendieck-edge-maps` names the bottom edge. Step 3 reads the first-quadrant page and finite filtration supplied by `thm-sp-grothendieck` and the bottom edge named by `lem-sp-grothendieck-edge-maps`. For total degree 0, 1, and 2, the only other rows are 1 and 2; their vanishing kills every incoming differential, and negative rows kill outgoing ones. Thus only the bottom graded piece remains. I checked the identity immersion and zero sheaf as small cases. The source was read at Tag 01F2 (`cohomology-lemma-Leray`) and the etale specialization at `etale-cohomology.tex`, `proposition-leray`; the proof is marked agent-written.

## Second reading by J1

- Item statement: checked against Tag 01F2 (`cohomology-lemma-Leray`) and `etale-cohomology.tex` label `proposition-leray`; hypotheses, edge-map direction, and degrees 0, 1, 2 agree.
- Step 1: checked against `lemma-weil-pbc-geometric-stalk-conservative`; the cited stalk criterion gives exactly the two sheaf vanishings used.
- Step 2: checked against `thm-sp-grothendieck`, `lem-weil-pbc-direct-image-preserves-injectives`, `def-weil-pbc-etale-cohomology`, `def-weil-pbc-direct-image`, and `lem-sp-grothendieck-edge-maps`; each cited statement supplies the spectral sequence, acyclicity, abutment identification, and bottom edge claimed.
- Step 3: checked against the first-quadrant filtration and edge-map statements of `thm-sp-grothendieck` and `lem-sp-grothendieck-edge-maps`; the incoming differential sources vanish for rows 1 and 2 or have negative first index, and outgoing differentials from row 0 have negative second index.
- New nodes: none; no duplicate, statement-only child, or Mathlib leaf was introduced. Existing generic spectral-sequence nodes were searched and used.
- Small cases checked: identity open immersion, empty/zero sheaf, and degree 0; all give the asserted identity isomorphism.

Changes: corrected the node's `created.item` to this item, replaced the informal source description with Tag 01F2 and both source labels, and recorded this second reading.
