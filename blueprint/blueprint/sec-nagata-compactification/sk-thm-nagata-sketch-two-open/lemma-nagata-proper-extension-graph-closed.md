+++
id = "lemma-nagata-proper-extension-graph-closed"
kind = "lemma"
title = "Closed image of the proper extension graph"
order = 286
lean = ["AlgebraicGeometry.TwoOpenSide.isProper_graph"]
uses = ["def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-two-open-graph-extensions", "lemma-nagata-proper-to-separated-target"]
+++
The morphism

$$
\gamma_i=(\psi_i,\mathrm{incl})\colon
V_i\longrightarrow U\times_SX_i
$$

is proper. In particular, its image is closed.

## Proof

By [def-nagata-two-open-graph-extensions], the morphism
$\psi_i\colon V_i\to U$ is proper. Regard
$\gamma_i\colon V_i\to U\times_SX_i$ as a morphism over $U$. The target
projection $U\times_SX_i\to U$ is separated because it is the base change
of the separated morphism $X_i\to S$. Apply
[lemma-nagata-proper-to-separated-target] with
$T=V_i$, $Y=U\times_SX_i$, and $B=U$. It makes $\gamma_i$ proper.
Proper morphisms are universally closed, so the image of $\gamma_i$ is
closed.
