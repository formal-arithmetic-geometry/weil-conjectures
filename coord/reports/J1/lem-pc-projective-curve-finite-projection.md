Files written:

- `dag/nodes/sec-picard-framework/lem-pc-projective-curve-finite-projection.json`: item split; no new nodes.
- `dag/nodes/sec-picard-framework/citations.json`: verbatim citations for step 1.

Attachments: none. The declaration `AlgebraicGeometry.exists_isFinite_toProjectiveLine` in `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/CurveProjection.lean:50-68` is sorry-free, but its explicit closed immersion and `topologicalKrullDim X = 1` hypotheses are narrower than the item's abstract projective-curve hypothesis, so it is not an attachment.

WANTED: none.

The imported item had an empty Mathlib search record and `blueprint.same_as: null`; I filled the required search record and changed `same_as` to `[]`. No new node was justified: every proof ingredient is already stated by the six cited nodes. The existing slopmaster2 coordinate-model declaration is sorry-backed, and is represented by the existing coordinate-model node rather than duplicated here.

## Review by J1

I read the item source and the projective-curve projection source in `WeilConjectures/AlgebraicGeometry/ProjectiveSpace/CurveProjection.lean`. The proof's projective embedding is supplied by `def-pc-projective-morphism`; the coordinate identification is exactly the statement of `lem-pc-projective-coordinate-model`; the infinite-field linear-pair choice is exactly `lem-pc-projective-curve-linear-pair`; the target morphism is the construction in `def-pc-linear-pair-morphism`; its compatibility and existence are stated by `lem-pc-linear-pair-morphism-gluing`; and finiteness is the conclusion of `lem-pc-linear-pair-morphism-finite`. I copied a verbatim sentence from each cited statement into `citations.json` and checked that all six nodes are existing, unmerged nodes.

The item hypotheses are used as follows: projectivity gives the closed immersion, integrality and dimension one are the hypotheses of the coordinate and linear-pair nodes, and infinitude of the field is the linear-avoidance hypothesis. The resulting glued map has target `\\mathbf P^1_k` and is finite by the final cited node. I tested the edge case `X = \\mathbf P^1_k`, where the identity projection is finite. The only correction needed was metadata: the Lean theorem found in slopmaster2 is narrower than the DAG statement, so I did not claim an attachment.

## Second reading by J1

- Step 1: checked against the blueprint proof and the statements of `def-pc-projective-morphism`, `lem-pc-projective-coordinate-model`, `lem-pc-projective-curve-linear-pair`, `def-pc-linear-pair-morphism`, `lem-pc-linear-pair-morphism-gluing`, and `lem-pc-linear-pair-morphism-finite`; each cited statement supplies the fact used, and the step is correctly non-elementary.
- New nodes: none; the DAG and blueprint searches found the cited existing nodes, so no duplicate or Mathlib leaf was created.
- Hypotheses and edge cases: projectivity supplies the closed immersion, integrality and dimension one feed the coordinate and linear-pair statements, and infinitude of $k$ feeds linear avoidance. The case $X=\\mathbf P^1_k$ gives the finite identity map; a field has dimension zero and is not a curve; the empty scheme is not integral.
- Lean audit: `AlgebraicGeometry.exists_isFinite_toProjectiveLine` is sorry-free but has explicit closed-immersion and Krull-dimension hypotheses, so it is not an exact attachment to this abstract statement; the coordinate-model declaration remains sorry-backed.

Changes made in this second reading: filled the item blueprint origin with the exact proof paragraph it realizes, and recorded this audit. No mathematical statement, proof step, citation, or node was otherwise changed.
