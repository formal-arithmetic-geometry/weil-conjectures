+++
id = "prop-weil-pbc-restriction-direct-image"
kind = "theorem"
title = "Restriction of the direct image to bounded constructibles"
order = 1302
uses = ["def-weil-pbc-constructible-direct-image-finiteness", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-operations", "lem-sp-finite-filtration-induction", "thm-constructible-serre", "thm-sp-truncation-e2"]
tags = ["latex:proposition"]
+++
Let $\Lambda=P_n$ be as in
[def-weil-pbc-constructible-direct-image-finiteness], let $u:S\to T$ be a
morphism of schemes, and suppose $\mathrm{FIN}(u,\Lambda;c)$. Then the
ambient functor $Ru_*$ restricts to an exact triangulated functor
$$
 Ru_*:\Dbc(S_{\Proet},\Lambda)\longrightarrow\Dbc(T_{\Proet},\Lambda),
$$
and if $K\in\Dbc(S_{\Proet},\Lambda)$ has cohomology in $[a,b]$, then
$Ru_*K$ has cohomology in $[a,b+c]$.

*Source note:* no Stacks Project entry states this conditional restriction.
Stacks' constructibility entries are Definition 61.29.1 ([Tag
09C1](https://stacks.math.columbia.edu/tag/09C1)) and Proposition 61.29.7
([Tag 09C7](https://stacks.math.columbia.edu/tag/09C7)), stated on a
Noetherian scheme for a Noetherian coefficient ring, together with Lemma
61.29.2 ([Tag 09C2](https://stacks.math.columbia.edu/tag/09C2)), which
realizes one constructible $K$ as $\Rlim K_n$ with each $K_n$ of bounded tor
amplitude, constructible cohomology and etale origin; the finiteness and
amplitude inputs are Lemma 59.92.2 ([Tag
095U](https://stacks.math.columbia.edu/tag/095U): for $f$ proper with all
fibres of dimension $\le n$ and every abelian torsion sheaf $\mathcal F$ on
$X_{\Et}$ one has $R^qf_*\mathcal F=0$ for $q>2n$) and Theorem 63.14.5 ([Tag
0GL0](https://stacks.math.columbia.edu/tag/0GL0): for $f$ separated of
finite presentation and $K\in D^+_{tors,c}(X_{\Et},\Lambda)$, $Rf_!K$ has
constructible cohomology sheaves). Difference: both are etale-site
statements about a single coefficient ring, with no amplitude shift, no
uniformity over a coefficient tower and no pro-etale site; the blueprint
adds the transport of these conditions to the small pro-etale sites as the
predicate $\mathrm{FIN}(u,\Lambda;c)$ and the amplitude shift by $c$.

## Proof

An object $K\in\Dbc(S_{\Proet},\Lambda)$ has constructible cohomology
sheaves $F_q=\mathcal H^q(K)$, zero outside the finite interval $[a,b]$. The
truncation-couple spectral sequence applied to the left exact $u_*$ gives
$$
 E_2^{p,q}=R^pu_*F_q\Longrightarrow\mathcal H^{p+q}(Ru_*K),
$$
with $E_2^{p,q}$ constructible for all $p,q$ by clause (i) of
[def-weil-pbc-constructible-direct-image-finiteness] and zero for $p>c$ by
clause (ii). For fixed $n=p+q$, the finite filtration of a convergent
spectral sequence exhibits $\mathcal H^n(Ru_*K)$ as a subquotient of a
finite extension of the constructible $E_\infty$-terms, hence constructible
by [thm-constructible-serre]; only $a\leq q\leq n$ and $p\leq c$
contribute, so $\mathcal H^n(Ru_*K)=0$ for $n\notin[a,b+c]$. Exactness is
the exactness of the ambient $Ru_*$ on the full triangulated subcategory
$\Dbc(S_{\Proet},\Lambda)$.
