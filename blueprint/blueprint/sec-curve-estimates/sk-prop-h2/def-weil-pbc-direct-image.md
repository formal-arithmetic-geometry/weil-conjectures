+++
id = "def-weil-pbc-direct-image"
kind = "definition"
title = "Direct image and its derived functor"
order = 938
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-kinjective-resolutions", "def-weil-pbc-scheme-conventions"]
+++
For a morphism [def-weil-pbc-scheme-conventions] $u:U\to V$, direct image is
the left exact functor

$$
 u_*:\Ab(U_{\Et})\longrightarrow\Ab(V_{\Et}),
 \qquad (u_*F)(W)=F(W\times_VU),
$$

where $W\to V$ runs over the objects of the small etale site
[def-weil-pbc-etale-site] $V_{\Et}$. If $K\to I(K)$ is a K-injective
resolution [def-weil-pbc-kinjective-resolutions], set

$$
 Ru_*K=u_*I(K),\qquad
 Ru_*:\Dplus(U_{\Et})\longrightarrow\Dplus(V_{\Et}),
$$

with $R^qu_*F=\mathcal H^q(Ru_*F)$ for a sheaf $F$. With a fixed coefficient
ring whose pullback is canonically identified with itself, the same functors
act on module sheaves.
