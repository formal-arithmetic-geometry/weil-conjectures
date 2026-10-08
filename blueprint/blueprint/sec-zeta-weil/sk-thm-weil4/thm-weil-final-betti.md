+++
id = "thm-weil-final-betti"
kind = "theorem"
title = "Weil conjectures IV: Betti symmetry"
order = 2935
uses = ["def-weil-betti-numbers", "def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-integral-frobenius-factor", "def-weil-ordinary-compact-cohomology", "prop-endpoints", "prop-integral-recovery", "prop-poincare-pairing", "prop-weil-betti-comparison", "thm-weil-final-integrality", "thm-weil-final-rh", "thm-weil-poincare-duality", "thm-weil-six-operations"]
+++
Fix a finite field
$k_0=\mathbf F_q$ of characteristic $p$, with algebraic closure
$k=\overline{\mathbf F}_q$.
Let $X_0/k_0$ be
smooth, proper and geometrically
connected of pure dimension $d\geq0$, and put $X=X_0\times_{k_0}k$.
Let $P_i\in\mathbf Z[T]$, $0\leq i\leq2d$, be the
integral Frobenius factors
provided by [thm-weil-final-integrality]: $P_i(0)=1$, and for
every $\ell\neq p$,

$$
P_i^{(\ell)}(T)=\det(1-TF_{i,\ell}\mid H^i(X,\mathbf Q_\ell)),
$$

where $F_{i,\ell}$ is
geometric Frobenius
on ordinary cohomology,
and $P_i^{(\ell)}$ means coefficientwise extension
$\mathbf Z\to\mathbf Q_\ell$.
For every integer $i$ with $0\leq i\leq2d$, set
$b_i=\deg P_i$; these are the
Betti numbers. Then

$$
b_i=\dim_{\Ql}H^i(X,\Ql)
\quad\text{for every prime }\ell\neq p,
\qquad b_i=b_{2d-i},
\qquad b_0=b_{2d}=1,
$$

where $H^i(X,\Ql)$ is the
ordinary cohomology group;
so the first dimension is independent of $\ell$. Moreover

$$
P_0(T)=1-T,
\qquad
P_{2d}(T)=1-q^dT.
$$

In particular, the rational function
$Z(X_0,T)=\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}\in\mathbf Q(T)$ of
[thm-weil-final-integrality] has a pole of order exactly $1$ at $T=1$
and, if $d\geq1$, a pole of order exactly $1$ at $T=q^{-d}$.

## Proof

The definition of the common Betti numbers is
[def-weil-betti-numbers]. The comparison in
[prop-weil-betti-comparison] gives
$b_i=\dim_{\Ql}H^i(X,\Ql)$, independently of $\ell$. The perfect pairing
has its canonical exceptional-inverse-image orientation supplied by
[thm-weil-six-operations] for the smooth proper structure morphism;
the duality interface [thm-weil-poincare-duality] and the pairing assembled in
[prop-poincare-pairing] together give $b_i=b_{2d-i}$; the endpoint calculation
[prop-endpoints] gives $b_0=b_{2d}=1$ and the two endpoint factors,
identified with $P_0,P_{2d}$ by [prop-integral-recovery].

For the poles, use the factorization
$Z(X_0,T)=\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}$ of
[thm-weil-final-integrality]. Over $\overline{\mathbf Q}$ write
$P_i(T)=\prod_{r=1}^{b_i}(1-\alpha_{i,r}T)$, the $\alpha_{i,r}$ being the
reciprocal roots. For $c\in\overline{\mathbf Q}^\times$, the order of
vanishing of $P_i$ at $T=c^{-1}$ is the number of $r$ with
$\alpha_{i,r}=c$. By [thm-weil-final-rh], every $\alpha_{i,r}$ satisfies
$|\tau(\alpha_{i,r})|=q^{i/2}$ for every complex embedding $\tau$.

Take $c=1$. Since $q>1$, $q^{i/2}=1$ only for $i=0$, so
$P_i(1)\neq0$ for $1\leq i\leq2d$, while $P_0(T)=1-T$ vanishes to
order exactly $1$ at $T=1$. As $P_0$ occurs with exponent $(-1)^{0+1}=-1$,
$Z(X_0,T)$ has a pole of order exactly $1$ at $T=1$.

Take $c=q^d$ with $d\geq1$. Since $|\tau(q^d)|=q^d=q^{i/2}$ only for
$i=2d$, one has $P_i(q^{-d})\neq0$ for $0\leq i<2d$ (for $i=0$ this is
also visible from $P_0(q^{-d})=1-q^{-d}\neq0$), while
$P_{2d}(T)=1-q^dT$ vanishes to order exactly $1$ at $T=q^{-d}$. As
$2d$ is even, $P_{2d}$ occurs with exponent $-1$, so $Z(X_0,T)$ has a
pole of order exactly $1$ at $T=q^{-d}$. (For $d=0$ the two points
coincide and $Z(X_0,T)=(1-T)^{-1}$.)
