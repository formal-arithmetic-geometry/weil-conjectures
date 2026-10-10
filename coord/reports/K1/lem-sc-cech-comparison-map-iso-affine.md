1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-cech-comparison-map-iso-affine.json` — statement, two proof steps, Mathlib searches, blueprint metadata, and split report.
- `dag/nodes/sec-picard-framework/lem-sc-cech-edge-map-identification.json` — new unsplit statement-only node; Mathlib searches found no match.
- `citations.json` — verbatim statement quotes for every citation in both steps.

2. Attachments: none.

3. WANTED: `literature/stacks-project/coherent.tex`, Lemma Tag 01XD; `literature/stacks-project/cohomology.tex`, Lemmas Tags 01EQ and 01ET. The repository contains the imported citation metadata but not the Stacks source files, so the split follows the cited tags and the existing neighboring nodes.

4. The imported item had no proof and no Mathlib search coverage beyond one grep. I supplied the missing proof route: spectral-sequence collapse from affine vanishing, followed by the canonical-edge-map identification. I added the edge-map identification node because the existing `lem-pc-cech-computes` statement gives only the abstract equality and does not say that it is the canonical map. I also recorded all three required Mathlib search kinds for the item and new node. The neighboring node statements were read directly: `lem-sc-cech-spectral` supplies the convergent Cech spectral sequence, `lem-pc-affine-vanishing` supplies higher-cohomology vanishing on affine intersections, `lem-sc-cech-comparison-map-naturality` defines the canonical map, and `lem-pc-cech-computes` supplies the resulting Cech/cohomology identification.

## Review by K1

I checked the target statement against the imported Stacks 01XD description and retained its hypotheses: a scheme, an open cover, affine finite intersections, and a quasi-coherent module. Step 1 cites only statements that provide the spectral sequence and affine vanishing; the row-collapse inference is the standard first-quadrant argument spelled out in the step. Step 2 cites the new edge-map statement, the existing definition/naturality statement for the canonical map, and the existing Cech-computation statement; each cited statement contains the exact fact used, as recorded verbatim in `citations.json`. The new node is strictly narrower than the item because it identifies the map without asserting that it is invertible. I searched the DAG and blueprint for an existing edge-map identification and found none. I tested the route on degree $p=0$ (the comparison is the restriction map on global sections) and on an affine scheme with the one-open cover (both sides are ordinary global sections); both cases agree with the claimed identification and isomorphism. The only correction to the imported record was adding the complete proof, the narrower child node, the missing Mathlib searches, and the explicit tool-use declaration for the neighboring Cech-computation lemma.
