+++
id = "lemma-nagata-intermediate-overlap-constructible"
kind = "lemma"
title = "Constructibility of the overlap image"
order = 287
lean = ["AlgebraicGeometry.TwoOpenSide.isClosedImmersion_intermediateGraph"]
uses = ["def-nagata-two-open-boundary-loci", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "lemma-nagata-boundary-loci", "lemma-nagata-proper-extension-graph-closed"]
+++
The image of

$$
U_i\longrightarrow
U\times_S(X_i\setminus\overline Z_{i,j})
$$

is constructible.

## Proof

The source and target are of finite type over the Noetherian scheme $S$.
The displayed morphism is an immersion and hence of finite type. Chevalley's
theorem makes its image constructible.
