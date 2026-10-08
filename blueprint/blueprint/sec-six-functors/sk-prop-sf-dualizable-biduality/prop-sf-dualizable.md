+++
id = "prop-sf-dualizable"
kind = "theorem"
title = "Perfect complexes are dualizable"
order = 2173
tags = ["latex:proposition"]
uses = ["def-sf-datum", "def-weil-derived-pullback-tensor-hom", "lem-sf-hom-finite-projective"]
+++
In the setting of [def-sf-datum], let $K\in D^b_{ctf}(X,\Lambda)$ be
quasi-isomorphic, locally on the site of $X$, to a bounded complex of finite
projective $\Lambda_X$-modules. Then
$K^\vee=R\mathcal H om_X(K,\Lambda_X)$ is perfect on $X$ and the
evaluation $K\otimes^L_{\Lambda_X}K^\vee\to\Lambda_X$ is defined.

## Proof

Choose locally a bounded complex $P^\bullet$ of finite projective
$\Lambda_X$-modules with a quasi-isomorphism $P^\bullet\to K$. By
[lem-sf-hom-finite-projective] the dual $P^{\bullet\vee}$ is again
bounded with finite projective terms, so $K^\vee$ is quasi-isomorphic to
$P^{\bullet\vee}$ and is perfect on $X$. The evaluation
$K\otimes^L_{\Lambda_X}K^\vee\to\Lambda_X$ is the counit of the
tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom], hence is defined.
