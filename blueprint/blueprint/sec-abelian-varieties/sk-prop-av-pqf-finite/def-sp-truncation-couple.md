+++
id = "def-sp-truncation-couple"
kind = "definition"
title = "The truncation couple of a bounded-below complex"
order = 520
uses = ["def-sp-exact-couple", "def-sp-grothendieck-abelian", "def-sp-kinjective-bridge", "def-sp-left-exact-additive"]
+++
Let $v:\mathcal A\to\mathcal B$ be left exact and additive
[def-sp-left-exact-additive] between Grothendieck abelian categories
[def-sp-grothendieck-abelian], and let $K\in\operatorname{Ch}^+(\mathcal A)$
be bounded below with $\mathcal H^q(K)=0$ for $q<a$. The *truncation couple*
of $K$ is the pair of bigraded objects

$$
 D^{p,q}=\mathcal H^{p+q}\bigl(Rv(\tau_{\leq q}K)\bigr),\qquad
 E^{p,q}=\mathcal H^{p+q}\bigl(Rv(\mathcal H^q(K)[-q])\bigr),
$$

obtained from the triangles

$$
 \tau_{\leq q-1}K\to\tau_{\leq q}K\to\mathcal H^q(K)[-q]\to
$$

by applying $Rv$ — the derived functor on $\operatorname{Ch}^+$ of
[def-sp-kinjective-bridge], the truncations $\tau_{\leq q}K$ and the shifted
cohomology sheaves being complexes and not objects — and taking cohomology,
with the structure maps $\alpha$,
$f$, $g$ of bidegrees $(-1,+1)$, $(+2,-1)$, $(0,0)$ as in
[def-sp-exact-couple] (the map $f:E^{p,q}\to D^{p+2,q-1}$ is the boundary
$\mathcal H^{p+q}(Rv\mathcal H^q(K)[-q])\to\mathcal H^{p+q+1}(Rv\,\tau_{\le
q-1}K)$ of the triangle).
