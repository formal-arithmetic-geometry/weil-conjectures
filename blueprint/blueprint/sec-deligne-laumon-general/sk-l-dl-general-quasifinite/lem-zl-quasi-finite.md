+++
id = "lem-zl-quasi-finite"
kind = "lemma"
title = "Quasi-finite morphisms: exactness and upper-weight bound"
order = 2818
lean = ["AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite", "AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.higherLowerShriek_zero_of_quasiFinite", "AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite"]
uses = ["def-weil-complex-weights", "def-weil-extension-by-zero", "def-weil-pbc-qbar-category", "lem-zl-finite-pushforward", "lemma-weil-pbc-finite-direct-image-exact", "prop-functor-package", "thm-pqf-zmt-factorization"]
+++
Let $g:Z_0\to Y_0$ be a separated quasi-finite morphism of separated
finite-type $k_0$-schemes.

1. For a $\Qlb$-Weil sheaf $\mathcal F$ on $Z_0$ (a Weil complex
concentrated in degree $0$) one has $R^ig_!\mathcal F=0$ for $i>0$.
Hence $g_!=\mathcal H^0Rg_!$ is exact on $\Qlb$-Weil sheaves, and
$\mathcal H^j(Rg_!K)=g_!\mathcal H^j(K)$ for every Weil complex $K$
and every $j$.
1. If $K\in D_{\le w}(Z_0)$, then $Rg_!K\in D_{\le w}(Y_0)$.

In particular $g_!$ preserves mixedness and upper weight bounds: if
$\mathcal F$ is a mixed $\Qlb$-Weil sheaf (of weights $\le w$), then so
is $g_!\mathcal F=Rg_!\mathcal F$.

## Proof

Since $Y_0$ is of finite type over a field, it is quasi-compact and
quasi-separated, so Zariski's main theorem in the form of the
quasi-finite factorization [thm-pqf-zmt-factorization] factors $g$
globally as

$$
Z_0\xrightarrow{\ j_0\ }\overline Z_0\xrightarrow{\ \bar g\ }Y_0
$$

with $j_0$ a quasi-compact open immersion and $\bar g$ finite; in
particular $\overline Z_0$ is again a separated finite-type
$k_0$-scheme. The factorization is defined over $k_0$, so it base
changes to $k$ and is compatible with the geometric Frobenius
automorphisms; all functors below therefore carry Weil structures. By
the composition isomorphism and the properness law of
[prop-functor-package] (clause 3), and since a finite morphism is
proper,

$$
Rg_!\simeq R\bar g_!\,j_{0!}\simeq R\bar g_*\,j_{0!}.
$$

*(1).* Extension by zero [def-weil-extension-by-zero] is exact: its
stalk at a geometric point of $Z$ is the stalk of the input, and at a
geometric point of the complement it is $0$. The finite direct image
$\bar g_*$ is exact by [lemma-weil-pbc-finite-direct-image-exact], so
$R\bar g_*=\bar g_*$. Both statements hold at every finite coefficient
stage and hence, by the common-stage construction of
[def-weil-pbc-qbar-category], for $\Qlb$-coefficients. Thus for a Weil
sheaf $\mathcal F$ we get $Rg_!\mathcal F\simeq\bar g_*j_{0!}\mathcal F$,
a complex concentrated in degree $0$, i.e. $R^ig_!\mathcal F=0$ for
$i\neq0$. Applying the exact functor $\bar g_*j_{0!}$ termwise gives
$\mathcal H^j(Rg_!K)=\bar g_*j_{0!}\mathcal H^j(K)=g_!\mathcal H^j(K)$.

*(2).* By (1) and the composition isomorphism it suffices to treat the
two pieces. For $j_0$: a closed point of $\overline Z_0$ either lies in
$Z_0$, where $j_{0!}K$ has the same stalk with the same local
Frobenius as $K$, or lies outside, where the stalk is $0$; so each
$\mathcal H^j(j_{0!}K)=j_{0!}\mathcal H^j(K)$ receives, from a
filtration of $\mathcal H^j(K)$ with punctually pure quotients of
weights $\le w+j$ as in [def-weil-complex-weights], the filtration
by the (exact) extensions by zero, whose quotients are again punctually
pure of the same weights. Hence $j_{0!}K\in D_{\le w}(\overline Z_0)$.
For $\bar g$: the finite pushforward bound [lem-zl-finite-pushforward]
gives $R\bar g_*j_{0!}K\in D_{\le w}(Y_0)$.

*In particular.* A mixed Weil sheaf $\mathcal F$ has a finite
filtration with punctually pure quotients; if $w$ is the largest of
their weights, then $\mathcal F\in D_{\le w}(Z_0)$ by
[def-weil-complex-weights]. By (2), $Rg_!\mathcal F\in D_{\le w}(Y_0)$,
and by (1) this complex is the sheaf $g_!\mathcal F$ in degree $0$;
so $g_!\mathcal F$ is mixed of weights $\le w$.
