+++
id = "thm-exc-direct-image-input-holds"
kind = "theorem"
title = "The direct-image finiteness input holds"
order = 1922
uses = ["def-exc-direct-image-input", "def-weil-pbc-constructible-complexes", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-kun-cd-sep-closed-point", "thm-dg-finite-type-constructibility", "thm-sc-finite-type-torsion-cd"]
+++
Let $k$ be a separably closed field, let $N$ be an integer prime to
$\operatorname{char}(k)$, and let $\Lambda$ be a finite commutative
ring annihilated by $N$. Then both clauses of the
direct-image finiteness input of
[def-exc-direct-image-input] hold over $k$.

## Proof

Clause (1) is [thm-dg-finite-type-constructibility]: for a morphism
$u:S\to T$ of finite type between finite-type $k$-schemes and a
constructible $\Lambda$-sheaf $F$, the derived direct image $Ru_*F$ is
bounded constructible, so each of its cohomology sheaves $R^qu_*F$ is
constructible on $T_{{\mathrm{et}}}$.

For clause (2), let $K$ be a separably closed field and let $W$ be a
finite-type $K$-scheme of dimension at most $d$. A separably closed
field has torsion cohomological dimension zero
([lem-kun-cd-sep-closed-point]), so
[thm-sc-finite-type-torsion-cd] bounds the torsion cohomological
dimension of $W$ by $2d+0=2d$; by the definition of that bound this is
the vanishing of $H^q(W,M)$ for every torsion sheaf $M$ and every
$q>2d$, which is the asserted clause.
