+++
id = "lem-kun-03qu-sep-closed"
kind = "lemma"
title = "Vanishing on a separably closed point"
order = 1533
uses = ["def-kun-separably-closed", "def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-site", "def-weil-pbc-geometric-stalks", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-geometric-stalks-exact"]
+++
If $K$ is separably closed and $F$ is an abelian sheaf on
$\Spec(K)_{\Et}$, then

$$
H^q(\Spec(K)_{\Et},F)=0\qquad\text{for every }q>0 .
$$

## Proof

Let $\bar s=\mathrm{id}:\Spec(K)\to\Spec(K)$. Since $K$ is
separably closed, every finite separable extension of $K$ is trivial,
so every etale $K$-scheme is a disjoint union of copies of $\Spec K$
(an etale $K$-algebra is a finite product of finite separable field
extensions); in particular $\bar s$ is a geometric point of the small
etale site [def-weil-pbc-etale-site], and every pointed
etale neighbourhood $(V,\bar v)$ of $\bar s$ admits a morphism
$(V,\bar v)\to(\Spec K,\bar s)$, namely the structure map, which sends
the chosen point to the unique point of $\Spec K$. Hence
$(\Spec K,\bar s)$ is terminal among the pointed etale
neighbourhoods of $\bar s$, and the defining colimit of
[def-weil-pbc-geometric-stalks] evaluates to $F_{\bar s}=F(\Spec K)=\Gamma(\Spec K_{\Et},F)$: the stalk functor at $\bar s$ *is*
the global-sections functor.
By [prop-weil-pbc-geometric-stalks-exact] it is exact, so the
global-sections functor is exact; by
[def-weil-pbc-etale-cohomology] the groups
$H^q(\Spec(K)_{\Et},F)$ are its right derived functors, which
therefore vanish for $q>0$.
