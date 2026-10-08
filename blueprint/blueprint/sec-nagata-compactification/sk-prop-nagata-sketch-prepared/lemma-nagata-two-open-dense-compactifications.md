+++
id = "lemma-nagata-two-open-dense-compactifications"
kind = "lemma"
title = "Properties of the chosen dense compactifications"
order = 264
lean = ["AlgebraicGeometry.exists_compactification_isSchemeTheoreticallyDominant"]
uses = ["def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-dense-compactification", "def-nagata-dense-refinement", "def-nagata-two-open-dense-compactifications", "prop-nagata-dense-refinement"]
+++
For $i=1,2$, the constructed $C_i$ is a scheme-theoretically dense
compactification of $U_i\to S$; in particular $X_i\to S$ is proper and
$U_i\hookrightarrow X_i$ is a quasi-compact open immersion.

## Proof

This is exactly [prop-nagata-dense-refinement], applied to each selected
compactification $C_i^0$.
