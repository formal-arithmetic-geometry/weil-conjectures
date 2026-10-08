+++
id = "lem-pc-cech-computes"
kind = "lemma"
title = "The Cech complex computes cohomology"
order = 610
uses = ["def-pc-morphism-conventions", "def-pc-scheme", "lem-pc-affine-vanishing", "lem-sc-cech-spectral"]
lean = ["AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_homology_iso_H"]
+++
Let $X$ be a scheme and let $\mathcal U:X=\bigcup_{i\in I}U_i$ be an
open covering such that all $U_{i_0\dots i_p}$ are affine. Then for any
quasi-coherent $\mathcal{O}_X$-module $\mathcal{F}$:

$$
\check H^p(\mathcal U,\mathcal{F})=H^p(X,\mathcal{F})\qquad\text{for all }p\ge0 .
$$

## Proof

Use the Cech-to-cohomology spectral sequence of
[lem-sc-cech-spectral] (whose proof – the double complex
$C^p(\mathcal U,I^q)$ of an injective resolution $I^\bullet$ of
$\mathcal{F}$ – is included there): it has
$E_2^{p,q}=\check H^p(\mathcal U,\underline H^q(\mathcal{F}))$ and converges to
$H^{p+q}(X,\mathcal{F})$. For $q>0$ and every multi-index $J$ the open $U_J$
is affine, so
$\underline H^q(\mathcal{F})(U_J)=H^q(U_J,\mathcal{F}|_{U_J})=0$ by
[lem-pc-affine-vanishing]; hence $E_1^{p,q}=0$ for $q>0$, the
spectral sequence degenerates at $E_2$, and the filtration of
$H^n(X,\mathcal{F})$ has only the nonzero piece
$E_\infty^{n,0}\cong\operatorname{gr}^n H^n(X,\mathcal F)$: thus
$\check H^p(\mathcal U,\mathcal{F})=H^p(X,\mathcal{F})$ for all $p$. (This is the
argument of Stacks Project, Cohomology of Schemes, Lemma 30.2.6, Tag
[01XD](https://stacks.math.columbia.edu/tag/01XD); its two
ingredients, Cech acyclicity of injective sheaves and the spectral
sequence of the double complex, are exactly the content of
[lem-sc-cech-spectral].)
