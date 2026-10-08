+++
id = "prop-sf-dualizable-hom"
kind = "theorem"
title = "Internal Hom through the coefficient dual"
order = 2174
tags = ["latex:proposition"]
uses = ["def-sf-datum", "def-weil-derived-pullback-tensor-hom", "lem-sf-hom-finite-projective"]
+++
In the setting of [def-sf-datum], let $K\in D^b_{ctf}(X,\Lambda)$ be
quasi-isomorphic, locally on the site of $X$, to a bounded complex of finite
projective $\Lambda_X$-modules. Then
$K^\vee\otimes^L_{\Lambda_X}M\to R\mathcal H om_X(K,M)$ is an
isomorphism for every $M\in D^b_{ctf}(X,\Lambda)$.

## Proof

Choose locally a bounded complex $P^\bullet$ of finite projective
$\Lambda_X$-modules with a quasi-isomorphism $P^\bullet\to K$, and let
$I(M)$ be a functorial K-injective replacement of $M$. Since the terms of
$P^\bullet$ are projective, $R\mathcal H om_X(K,M)$ is represented by
$\mathcal H om^\bullet_X(P^\bullet,I(M))$, and termwise
$\mathcal H om_X(P^j,I(M)^k)=P^{j\vee}\otimes_{\Lambda_X}I(M)^k$ by
[lem-sf-hom-finite-projective], the identification being compatible
with differentials. Hence
$R\mathcal H om_X(K,M)\cong P^{\bullet\vee}\otimes_{\Lambda_X}I(M)\cong K^\vee\otimes^L_{\Lambda_X}M$, which is the displayed isomorphism, the
$K^\vee$-side of both objects being the coefficient dual of
[def-weil-derived-pullback-tensor-hom].
