+++
id = "lemma-nagata-intermediate-separated"
kind = "lemma"
title = "Separatedness of the intermediate schemes"
order = 291
lean = ["AlgebraicGeometry.TwoOpenSide.isSeparated_intermediateHom"]
uses = ["def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "lemma-nagata-boundary-loci", "lemma-nagata-intermediate-overlap-closed", "lemma-nagata-intermediate-overlap-constructible", "lemma-nagata-intermediate-overlap-specialization-closed", "lemma-nagata-intermediate-specialization-boundary", "lemma-nagata-separated-two-open-cover"]
+++
Each $W_i\to S$ is separated and of finite type.

## Proof

The opens $U$ and $X_i\setminus\overline Z_{i,j}$ cover $W_i$. The first
is separated and of finite type over $S$ by the section hypotheses. The
second has those properties because it is open in the proper scheme
$X_i\to S$. Their overlap map is the closed immersion supplied by
[lemma-nagata-intermediate-overlap-closed]. Apply
[lemma-nagata-separated-two-open-cover] to these two opens to obtain
separatedness of $W_i\to S$. Finite type is local on this finite open
cover, so $W_i\to S$ is also of finite type.
