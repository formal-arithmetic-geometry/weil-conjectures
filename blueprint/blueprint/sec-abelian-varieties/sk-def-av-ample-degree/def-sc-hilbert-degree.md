+++
id = "def-sc-hilbert-degree"
kind = "definition"
title = "The Hilbert degree of an ample line bundle"
lean = ["AlgebraicGeometry.Scheme.Hom.degree"]
order = 438
uses = ["def-sc-ample"]
+++
Let $X$ be a proper scheme of dimension $g$ over a field $k$
and $\mathcal M$ an ample invertible
$\mathcal O_X$-module. The *degree* of $X$ with respect to
$\mathcal M$ is

$$
\deg_{\mathcal M}(X):=g!\cdot
\bigl(\text{leading coefficient of }m\mapsto\chi(X,\mathcal
M^{\otimes m})\bigr),
$$

the leading coefficient being taken for the function
$m\mapsto\chi(X,\mathcal M^{\otimes m})$ of $m$. That this
function is a numerical polynomial in $m$ of total degree at most
$g$ – the Hilbert polynomial of $\mathcal M$ – so that the
leading coefficient, and hence the degree, is well defined, is
[lem-sc-hilbert-polynomial], and it is not part of the
definition.
