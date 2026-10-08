+++
id = "lem-sc-deg-pullback-finite"
kind = "lemma"
title = "Degree of the pullback under a finite morphism"
lean = ["AlgebraicGeometry.Scheme.Hom.degree_pullback"]
order = 484
uses = ["def-sc-ample", "def-sc-function-field", "def-sc-hilbert-degree", "lem-sc-hilbert-polynomial"]
+++
Let $f:X\to Y$ be a finite surjective morphism of proper
varieties over a field $k$, let $\mathcal M$ be an
ample invertible $\mathcal O_Y$-module,
and let $\deg(f)=[k(X):k(Y)]$ be the degree of the finite
dominant morphism $f$
(function fields). Then

$$
\deg_{f^*\mathcal M}(X)=\deg(f)\deg_{\mathcal M}(Y),
$$

where the degrees are those of [def-sc-hilbert-degree].

## Proof

*Reference: Stacks Project, Varieties, Lemma 33.45.11,
[Tag 0BEX](https://stacks.math.columbia.edu/tag/0BEX).* By the
projection formula,

$$
\chi(X,f^*\mathcal M^{\otimes m})
=\chi(Y,f_*f^*\mathcal M^{\otimes m})
=\chi(Y,f_*\mathcal O_X\otimes\mathcal M^{\otimes m}).
$$

The coherent sheaf $f_*\mathcal O_X$ has generic rank
$[k(X):k(Y)]=\deg(f)$ (the stalk at the generic point of $Y$ is
$k(X)$, of degree $\deg(f)$ over $k(Y)$), and for a coherent
sheaf $\mathcal E$ of generic rank $r$ on the proper
$g$-dimensional variety $Y$, the numerical polynomial
$m\mapsto\chi(Y,\mathcal E\otimes\mathcal M^{\otimes m})$ has the
same leading coefficient as
$r\cdot\chi(Y,\mathcal M^{\otimes m})$ (both are polynomials of
degree at most $g$ whose difference has degree at most $g-1$:
this follows from the additivity of $\chi$ in short exact
sequences and devissage, reducing to the case $\mathcal E$
invertible, where $\chi(Y,\mathcal M^{\otimes m}\otimes\mathcal E)$ and $\chi(Y,\mathcal M^{\otimes m})$ differ by a polynomial
of degree at most $g-1$ by [lem-sc-hilbert-polynomial] (*Stacks
Project, Varieties, Lemma 33.45.1, [Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)*), the numerical-polynomial
lemma, applied to the two invertible modules). Hence the degrees
of [def-sc-hilbert-degree] satisfy
$\deg_{f^*\mathcal M}(X)=\deg(f)\deg_{\mathcal M}(Y)$.
