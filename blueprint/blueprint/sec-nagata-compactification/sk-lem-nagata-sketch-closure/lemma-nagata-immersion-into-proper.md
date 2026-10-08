+++
id = "lemma-nagata-immersion-into-proper"
kind = "lemma"
title = "The immersion construction is a compactification"
order = 80
lean = ["AlgebraicGeometry.HasCompactification.of_isImmersion"]
uses = ["def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-immersion-compactification", "lemma-nagata-immersion-open-in-scheme-image", "lemma-nagata-open-immersion-qc-over-separated-target"]
+++
The constructed factorization $\mathsf C(g)$ is a compactification of
$X\to S$.

## Proof

The first map is a quasi-compact open immersion by
[lemma-nagata-immersion-open-in-scheme-image]. The second map is the
composite of a closed immersion with the proper map $Y\to S$, hence is
proper. If the given over-$S$ structure is
$g;(Y\to S)=f$, the factorization equality gives the required structural
equality explicitly:

$$
g^{\mathrm{im}};g_{\mathrm{im}};(Y\to S)
=g;(Y\to S)=f.
$$
