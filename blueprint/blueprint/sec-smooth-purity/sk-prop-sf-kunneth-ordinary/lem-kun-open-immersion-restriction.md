+++
id = "lem-kun-open-immersion-restriction"
kind = "lemma"
title = "Inverse image along an open immersion is a left inverse of direct image"
order = 1699
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "lem-kun-leray-bdd"]
+++
Let $j:U\to X$ be an
open immersion. Then
$j^{-1}j_*=\mathrm{id}$ on $\Ab(U_{\Et})$, and for every
$F\in D(U_{\Et})$ the canonical morphism
$\RGamma(X_{\Et},Rj_*F)\to\RGamma(U_{\Et},F)$ of
[lem-kun-leray-bdd] is an isomorphism (Leray for $j$).

## Proof

For an etale $V\to U$, the direct image of
[def-weil-pbc-direct-image] gives
$(j_*F)(V)=F(V\times_XU)=F(V)$, because
$V\times_XU=V$ since $V\to X$ factors through the open $U$; this
is $j^{-1}j_*=\mathrm{id}$. The second assertion is
[lem-kun-leray-bdd] applied to $j$.
