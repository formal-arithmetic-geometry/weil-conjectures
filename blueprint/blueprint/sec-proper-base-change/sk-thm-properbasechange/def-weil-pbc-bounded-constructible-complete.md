+++
id = "def-weil-pbc-bounded-constructible-complete"
kind = "definition"
title = "Bounded constructible complete category"
order = 1300
uses = ["def-weil-pbc-bounded-constructible-tower", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-intrinsic-completion"]
+++
Assume $T$ is noetherian of finite dimension and the torsion orders are
invertible on $T$. Define $\Dbc(T_{\Proet},A)$ to be the full subcategory of
derived $I$-complete objects, in the sense of the intrinsic completion,
whose reduction tower has compatible etale origins
[def-weil-pbc-etale-origin-witness] and is uniformly bounded constructible
in the sense of the bounded constructible tower.

This is the category $D_{cons}(X,\Lambda)$ of Stacks Project, Definition
61.29.1 ([Tag 09C1](https://stacks.math.columbia.edu/tag/09C1), Section
61.29, [Tag 09C0](https://stacks.math.columbia.edu/tag/09C0)): the Stacks
definition assumes a Noetherian ring $\Lambda$ with an ideal $I$ and calls
$K\in D(X_{\Proet},\Lambda)$ constructible if $K$ is derived complete and
$K\otimes^L_\Lambda\underline{\Lambda/I}$ has constructible cohomology
sheaves and locally finite tor dimension, whereas the form used here
requires, over $A=\mathcal O_E$ and $I=(\varpi)$, a uniformly bounded
constructible reduction tower with compatible etale origins.
