+++
id = "lem-pc-universal-divisor"
kind = "lemma"
title = "The universal divisor"
order = 795
uses = ["def-pc-divisor-line-bundle", "def-pc-hilb-functor", "def-pc-relative-effective-cartier", "def-sc-effective-cartier-divisor", "lem-pc-cartier-criterion", "lem-pc-recd-pullback", "thm-pc-hilb-curves"]
+++
(Picard Schemes of Curves, Remark 44.3.7, Tag
[0B9J](https://stacks.math.columbia.edu/tag/0B9J).) Let $X$ be as
in [thm-pc-hilb-curves] and let $d\geq0$. There is a relative
effective Cartier divisor

$$
D_{\mathrm{univ}}\subset \underline{\operatorname{Hilb}}^{d+1}_{X/k}\times_kX
$$

over $\underline{\operatorname{Hilb}}^{d+1}_{X/k}$ (a universal closed object, which is
an effective Cartier divisor via [lem-pc-cartier-criterion]), and
$\mathcal{O}(D_{\mathrm{univ}})$ is the associated invertible module; for a
$k$-rational point $[D]\in\underline{\operatorname{Hilb}}^{d+1}_{X/k}$ corresponding to
an effective Cartier divisor $D\subset X$ of degree $d+1$, the restriction
of $\mathcal{O}(D_{\mathrm{univ}})$ to the fibre $[D]\times X\cong X$ is
$\mathcal{O}_X(D)$.

## Proof

By [thm-pc-hilb-curves](1) the functor $\operatorname{Hilb}^{d+1}_{X/k}$ is
representable by
$H:=\underline{\operatorname{Hilb}}^{d+1}_{X/k}$; by the definition of
representability ([def-pc-hilb-functor]) there is a universal
element

$$
Z_{\mathrm{univ}}\in\operatorname{Hilb}^{d+1}_{X/k}(H),
$$

i.e. a closed subscheme $Z_{\mathrm{univ}}\subset X_H=H\times_kX$
finite locally free of degree $d+1$ over $H$. Apply
[lem-pc-cartier-criterion] ((1)$\Rightarrow$(2)) to the smooth
morphism of relative dimension $1$
$H\times_kX\to H$ (the base change of $X\to k$ along $H\to k$: base
changes of smooth morphisms are smooth, the standard statement) and
the closed subscheme $Z_{\mathrm{univ}}$: it is a relative effective
Cartier divisor $D_{\mathrm{univ}}$ on $H\times_kX/H$
([def-pc-relative-effective-cartier]). Its associated invertible
module is $\mathcal{O}(D_{\mathrm{univ}})$
([def-pc-divisor-line-bundle]). For a $k$-rational point
$[D]\in H$ corresponding to an effective Cartier divisor $D\subset X$
of degree $d+1$: the fibre of the universal element over $[D]$ is, by
the universality of $Z_{\mathrm{univ}}$, exactly the closed subscheme
$D$ of the fibre
$X_{[D]}=X$ (the point $[D]$ of $H$ corresponds, via the
identification of [thm-pc-hilb-curves](2), to the element $D$ of
$\operatorname{Hilb}^{d+1}_{X/k}(k)$: the fibre of the universal object over $[D]$
is that element, by the very definition of universality); hence the
restriction of $D_{\mathrm{univ}}$ to the fibre
$\{[D]\}\times X\cong X$ is the effective Cartier divisor $D$ and, by
the base change property of the divisor module
([lem-pc-recd-pullback], or directly:
$\mathcal{O}(D_{\mathrm{univ}})|_{\{[D]\}\times X} =\mathcal{O}_X(D)$), the restriction of
$\mathcal{O}(D_{\mathrm{univ}})$ is $\mathcal{O}_X(D)$.
