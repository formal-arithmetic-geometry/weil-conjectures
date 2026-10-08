+++
id = "lemma-nagata-intermediate-overlap-closed"
kind = "lemma"
title = "Closedness of the intermediate overlap"
order = 290
lean = ["AlgebraicGeometry.TwoOpenSide.isClosedImmersion_intermediateGraph"]
uses = ["def-nagata-two-open-boundary-loci", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "lemma-nagata-boundary-loci", "lemma-nagata-intermediate-overlap-constructible", "lemma-nagata-intermediate-overlap-specialization-closed", "lemma-nagata-proper-extension-graph-closed"]
+++
The canonical immersion

$$
U_i\longrightarrow
U\times_S(X_i\setminus\overline Z_{i,j})
$$

is a closed immersion.

## Proof

By [lemma-nagata-intermediate-overlap-constructible], the image is
constructible. By
[lemma-nagata-intermediate-overlap-specialization-closed], it is stable
under specialization. The target is Noetherian, so the image is closed.
Factor the given immersion as a closed immersion into an open subscheme
$T'\subseteq T$, where
$T=U\times_S(X_i\setminus\overline Z_{i,j})$. Over $T'$ the map is a
closed immersion by construction. Over the open complement of its closed
image in $T$, its inverse image is empty, hence is also a closed immersion.
These two opens cover $T$: every point outside $T'$ is outside the image.
Since being a closed immersion is local on the target, the original
immersion is a closed immersion.
