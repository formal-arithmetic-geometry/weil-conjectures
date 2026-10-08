+++
id = "lem-sp-truncation-couple-exact"
kind = "lemma"
title = "The truncation couple is an exact couple"
order = 1210
uses = ["def-sp-exact-couple", "def-sp-grothendieck-abelian", "def-sp-left-exact-additive", "def-sp-truncation-couple", "lem-sp-long-exact-of-triangle"]
+++
Let $v:\mathcal A\to\mathcal B$ be left exact and additive
[def-sp-left-exact-additive] between Grothendieck abelian categories
[def-sp-grothendieck-abelian], and let $K\in\operatorname{Ch}^+(\mathcal A)$
be bounded below with $\mathcal H^q(K)=0$ for $q<a$. Then the truncation
couple [def-sp-truncation-couple] of $K$, with the structure maps $\alpha$,
$f$, $g$ of bidegrees $(-1,+1)$, $(+2,-1)$, $(0,0)$ of
[def-sp-truncation-couple], is an exact couple [def-sp-exact-couple].

## Proof

Exactness of a couple means the three identities of subobjects of
[def-sp-exact-couple] in every bidegree. Fix $q$ and apply the homological
functor $\mathcal H^{p+q}\circ Rv$ to the distinguished triangle $\tau_{\leq
q-1}K\to\tau_{\leq q}K\to\mathcal H^q(K)[-q]\to$ of
[def-sp-truncation-couple]; by [lem-sp-long-exact-of-triangle] the result is
the long exact sequence

$$
 \cdots\to D^{p+1,q-1}\xrightarrow{\ \alpha\ }D^{p,q}
 \xrightarrow{\ g\ }E^{p,q}\xrightarrow{\ f\ }D^{p+2,q-1}\to\cdots,
$$

where the three maps are the ones recorded in
[def-sp-truncation-couple], and the exactness of this sequence at its three
displayed spots is precisely $\ker\alpha=\operatorname{im}f$,
$\ker f=\operatorname{im}g$ and $\ker g=\operatorname{im}\alpha$ in the
bidegree $(p,q)$. As $q$ and $p$ are arbitrary this is the assertion.
