+++
id = "def-weil-pbc-proetale-modules"
kind = "definition"
title = "Finite coefficients on the pro-etale site"
order = 1233
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "def-weil-pbc-proetale-site"]
+++
For a finite discrete ring $\Lambda$, let $\Lambda_{T,\Proet}$ be the
sheafification of

$$
 U\longmapsto\operatorname{Cont}(\pi_0(|U|),\Lambda)
$$

on the small pro-etale site [def-weil-pbc-proetale-site]. Let
$\Mod(T_{\Proet},\Lambda)$ be its abelian category of module sheaves and
define

$$
 D(T_{\Proet},\Lambda)=
 \mathsf{Cpx}(\Mod(T_{\Proet},\Lambda))
 [\{\text{quasi-isomorphisms}\}^{-1}].
$$

The subcategories $\Dplus(T_{\Proet},\Lambda)$ and
$\Dbc(T_{\Proet},\Lambda)$ are defined by lower boundedness and by pullback
of the bounded constructible etale objects of
[def-weil-pbc-constructible-complexes], respectively.
