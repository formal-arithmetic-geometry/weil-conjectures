+++
id = "def-sp-double-complex-total"
kind = "definition"
title = "First-quadrant double complexes, total complex and the two filtrations"
order = 516
uses = ["def-sp-abelian", "def-sp-filtration"]
+++
Let $\mathcal C$ be an abelian category [def-sp-abelian]. A *double complex*
$D^{\bullet,\bullet}$ in $\mathcal C$ is a family of objects $D^{p,q}$
($p,q\in\mathbb Z$) with morphisms

$$
 d_I:D^{p,q}\to D^{p+1,q},\qquad d_{II}:D^{p,q}\to D^{p,q+1}
$$

such that $d_I\circ d_I=0$, $d_{II}\circ d_{II}=0$ and
$d_I\circ d_{II}=d_{II}\circ d_I$. It is *first-quadrant* if $D^{p,q}=0$
unless $p\geq0$ and $q\geq0$. For each $p$ the *$p$-th column*
$(D^{p,\bullet},d_{II})$ and for each $q$ the *$q$-th row*
$(D^{\bullet,q},d_I)$ are complexes; their cohomology objects are written

$$
 H^q_{II}(D^{p,\bullet}):=H^q(D^{p,\bullet},d_{II}),\qquad
 H^p_{I}(D^{\bullet,q}):=H^p(D^{\bullet,q},d_I).
$$

Since $d_I$ commutes with $d_{II}$, it induces morphisms
$H^q_{II}(D^{p,\bullet})\to H^q_{II}(D^{p+1,\bullet})$, making
$H^q_{II}(D)$ a complex in the first index, with cohomology
$H^p_IH^q_{II}(D)$; symmetrically $d_{II}$ makes $H^p_I(D)$ a complex in the
second index, with cohomology $H^q_{II}H^p_I(D)$.

For a first-quadrant double complex the *total complex*
$\operatorname{Tot}(D)$ is

$$
 \operatorname{Tot}(D)^n:=\bigoplus_{p+q=n}D^{p,q},\qquad
 d|_{D^{p,q}}:=d_I+(-1)^pd_{II}:D^{p,q}\to D^{p+1,q}\oplus D^{p,q+1};
$$

the sum is finite (only $0\leq p\leq n$ contribute, and
$\operatorname{Tot}(D)^n=0$ for $n<0$), and $d\circ d=0$ because
$d_I^2=d_{II}^2=0$ and the two cross terms $(-1)^{p+1}d_{II}d_I$ and
$(-1)^pd_Id_{II}$ cancel.

The *first* and *second filtrations* of $\operatorname{Tot}(D)$ are the
decreasing filtrations [def-sp-filtration]

$$
 {}'F^p\operatorname{Tot}(D)^n:=\bigoplus_{i\geq p}D^{i,n-i},\qquad
 {}''F^q\operatorname{Tot}(D)^n:=\bigoplus_{j\geq q}D^{n-j,j}
$$

(filtration by the first, resp. the second, degree). Both are filtrations by
subcomplexes, since $d_I$ raises the first degree by one and preserves the
second, while $d_{II}$ preserves the first and raises the second. In total
degree $n$ both satisfy $F^0\operatorname{Tot}(D)^n=\operatorname{Tot}(D)^n$
and $F^{n+1}\operatorname{Tot}(D)^n=0$, so they are finite in each degree.
Their graded pieces are the complexes

$$
 \operatorname{gr}^p_{'F}\operatorname{Tot}(D)=D^{p,\bullet-p}
 \ \text{with differential }(-1)^pd_{II},\qquad
 \operatorname{gr}^q_{''F}\operatorname{Tot}(D)=D^{\bullet-q,q}
 \ \text{with differential }d_I .
$$

(Stacks Project, Homological Algebra: double complexes and their associated
total complexes, and the two filtrations used for the spectral sequences of
a double complex.)
