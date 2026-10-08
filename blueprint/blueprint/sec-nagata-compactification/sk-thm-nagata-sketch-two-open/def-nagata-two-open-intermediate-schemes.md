+++
id = "def-nagata-two-open-intermediate-schemes"
kind = "definition"
title = "Intermediate two-open schemes"
order = 285
lean = ["AlgebraicGeometry.TwoOpenSide.interior"]
uses = ["def-nagata-two-open-boundary-loci", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-prepared-boundaries", "lemma-nagata-key-boundary-disjointness"]
+++
For $\{i,j\}=\{1,2\}$, define

$$
X_i^\circ=X_i\setminus\overline Z_{i,j}
$$

and glue the open subschemes $U_i\subseteq U$ and
$U_i\subseteq X_i^\circ$ by the identity. Denote the result by

$$
W_i=U\amalg_{U_i}X_i^\circ.
$$

The construction includes the two open immersions
$U\hookrightarrow W_i$ and $X_i^\circ\hookrightarrow W_i$ and the induced
structural map $W_i\to S$.
