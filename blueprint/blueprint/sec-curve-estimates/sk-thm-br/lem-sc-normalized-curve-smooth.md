+++
id = "lem-sc-normalized-curve-smooth"
kind = "lemma"
title = "The normalized curve over a perfect field is smooth"
order = 918
uses = ["def-sc-normalization", "lem-sc-normal-dim1-dvr", "lem-sc-regular-dim1-dvr", "lem-sc-smooth-regular"]
+++
Let $X$ be an integral scheme of finite type over a perfect field
$k$ with $\dim X=1$, and
$\nu:X^{\nu}\to X$ its normalization
([def-sc-normalization]). Then $X^{\nu}$ is smooth over
$k$.

## Proof

By construction $X^{\nu}$ is normal (its structure sheaf is
integrally closed in $k(X)$). Every local ring of $X^{\nu}$
is a one-dimensional noetherian normal local domain, hence a
discrete valuation ring by [lem-sc-normal-dim1-dvr]; hence
$X^{\nu}$ is regular at every point
([lem-sc-regular-dim1-dvr]). Over the perfect field $k$, a
regular scheme of finite type is smooth: at a point $x$, the
residue field $k(x)$ is a finite extension of the perfect field
$k$, hence separable over $k$, and a regular local
$k$-algebra essentially of finite type over $k$ with residue
field separable over $k$ is smooth over $k$ (*reference:
Stacks Project, Commutative Algebra, Lemma 10.140.5,
[Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)*; smoothness over the field $k$ is equivalent to
geometric regularity over $k$, so it stays regular after any
base change by a field extension), which is exactly the defining
property of smoothness of $X^{\nu}\to\operatorname{Spec}k$ at
$x$ (flat and geometrically regular fibres, as in
[lem-sc-smooth-regular]).
