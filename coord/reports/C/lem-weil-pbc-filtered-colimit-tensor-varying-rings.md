# Delivery report: `lem-weil-pbc-filtered-colimit-tensor-varying-rings`

1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-filtered-colimit-tensor-varying-rings.json`: stage-1 split with a complete parent proof; no child nodes.

2. Attachments:

None. The Mathlib searches already recorded on the node find only fixed-ring tensor-colimit results, so there is no exact Lean declaration to attach.

3. WANTED:

None.

4. What was repaired:

The returned delivery concern was that proof arguments had been placed in new nodes while those nodes remained unsplit. This repair keeps the complete common-stage argument in the parent node. The proof follows Stacks Sheaves Lemma 007K and uses Algebra Lemma 10.12.9 (Tag 00DD) as the fixed-ring model: construct the map by the colimit universal property, move finitely many representatives and relations to a common later stage for surjectivity and injectivity, then check the inverse and naturality on pure-tensor generators. The varying coefficient ring is handled by advancing the finitely many coefficients to one common stage. `proof_deps` is the union of the step uses.

## Review by C

I checked the statement against the cited filtered-colimit/tensor assertion in Stacks Sheaves Lemma 007K and the common-stage presentation proof in Algebra Lemma 10.12.9 (Tag 00DD). The construction is balanced by semilinearity; directedness supplies common stages for representatives and coefficients; pure tensors give surjectivity and generation gives the naturality check. The injectivity paragraph explicitly handles the finite list of tensor and scalar relations, which is the point needed when the coefficient rings vary. No child node contains proof text while unsplit, and the parent proof dependencies equal the union of its step uses. The existing `def-weil-pbc-category-colimit` dependency is valid and the recorded three-way Mathlib search supports the absence of an exact varying-ring theorem.
