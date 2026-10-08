+++
id = "lemma-nagata-boundary-disjoint-persists"
kind = "lemma"
title = "Disjoint boundary closures persist"
order = 269
lean = ["AlgebraicGeometry.disjoint_range_strictTransformMap_of_disjoint"]
uses = ["def-nagata-strict-transform", "lemma-nagata-strict-transform-closure-characterization", "lemma-nagata-strict-transform-restrict"]
+++
If $\overline Z_{i,i}$ and $\overline Z_{i,j}$ are disjoint, then their
strict transforms remain disjoint after every further $V_i$-admissible
blow-up.

## Proof

Let $b\colon X'_i\to X_i$ be a further $V_i$-admissible blow-up. By
[lemma-nagata-strict-transform-restrict], the strict transform of
$\overline Z_{i,k}$ is the closure of its restriction over the open on
which $b$ is an isomorphism. It is therefore contained in
$b^{-1}(\overline Z_{i,k})$. The inverse images of the disjoint closed
subschemes $\overline Z_{i,i}$ and $\overline Z_{i,j}$ are disjoint, so
their contained strict transforms are disjoint as well.
