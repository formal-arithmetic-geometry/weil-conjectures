# Stage 1 report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-open-curve-gm-direct-image-cohomology.json`: statement, split proof, two steps; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-open-curve-boundary-higher-direct-image-vanishing.json`: statement-only helper; Mathlib searches found no match.
- `dag/nodes/sec-curve-estimates/lem-sc-open-curve-etale-leray-low-degree.json`: statement-only helper; Mathlib searches found no match.
- `citations.json`: verbatim statement excerpts for both cited steps.

2. Attachments: none. No exact declaration tagged `(blueprint: lem-sc-open-curve-gm-direct-image-cohomology)` exists in the Lean source, and the item has no `lean_audit` declaration.

3. WANTED: none; the Stacks etale-cohomology source is present locally.

4. Issues found: the imported item was statement-only despite its source sentence asserting a nontrivial stalk and Leray argument. I made both hidden facts explicit as statement-only nodes. The existing generic-point `R^1j_*G_m` node does not cover an open complement, so it was not cited.

## Review by C1

I read the item, the `sec-curve-estimates` chapter and `sk-thm-br` unit, and the Stacks discussion preceding Tag 03RM. I searched the complete DAG and blueprint for direct-image, strict-henselization, Hilbert-90, Brauer, and Leray statements. The only related existing nodes were generic-point vanishing and a general topological Leray spectral sequence; neither states the needed etale open-complement result, so I created the two helpers.

Step 1 cites the boundary-vanishing helper, whose statement explicitly supplies zero stalks for q=1,2 and names the strict-henselization/Hilbert-90/Brauer computation. Step 2 cites the low-degree Leray helper, whose hypotheses and conclusion exactly give the comparison map for q=0,1,2. The item hypotheses (algebraically closed k, proper smooth connected Cbar, finite S, open immersion j, and G_m on the small etale site) match the source and the helper contexts. I checked edge cases S empty (j is the identity) and C=A^1 in P^1 with one boundary point; the claimed comparison specializes correctly. Every citation quote is copied verbatim from its node statement.
