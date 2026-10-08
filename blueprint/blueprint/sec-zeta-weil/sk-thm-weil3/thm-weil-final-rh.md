+++
id = "thm-weil-final-rh"
kind = "theorem"
title = "Weil conjectures III: Riemann hypothesis"
order = 2932
lean = ["AlgebraicGeometry.Scheme.weil_conjectures", "AlgebraicGeometry.WeilRiemannHypothesis"]
uses = ["def-weil-finite-field-fiber", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-integral-frobenius-factor", "def-weil-numbers", "def-weil-ordinary-compact-cohomology", "def-weil-ordinary-reciprocal-roots", "lem-embedding-extension", "prop-arithmetic-roots", "prop-integral-recovery", "prop-weight-purity-roots", "prop-weil-realization-independent-degrees", "thm-weil-deligne-purity", "thm-weil-final-integrality"]
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
For every integer $i$ with $0\leq i\leq2d$, put
$r_i=\deg P_i$ and $P_i^\#(U)=U^{r_i}P_i(U^{-1})$. A
reciprocal root
$\alpha\in\overline{\mathbf Q}$ means a root of $P_i^\#$; put
$\beta=\alpha^{-1}$, the corresponding
ordinary root. Every
reciprocal root $\alpha$ is a
algebraic integer and a
Weil number for $q$ of weight $i$:

$$
|\tau(\alpha)|=q^{i/2}
$$

for every embedding $\tau:\mathbf Q(\alpha)\hookrightarrow\mathbf C$. Then
$|\tau(\beta)|=q^{-i/2}$ for every embedding
$\tau:\mathbf Q(\beta)\hookrightarrow\mathbf C$.

## Proof

The reversed polynomial is monic because the constant coefficient is one and
the coefficients are integral by [prop-integral-recovery]; hence its
roots are algebraic integers. The root/eigenvalue identification is
[def-weil-ordinary-reciprocal-roots]. For a root $\alpha$,
[lem-embedding-extension] extends every embedding of
$\mathbf Q(\alpha)$ to an isomorphism $\Qlb\simeq\mathbf C$, and
[prop-weight-purity-roots] gives
$|\tau(\alpha)|=q^{i/2}$. In the terminology of
[def-weil-numbers], this is precisely the $q$-Weil condition; taking
inverses gives the ordinary-root bound. The arithmetic formulation and the
degree independence are also recorded in [prop-arithmetic-roots] and
[prop-weil-realization-independent-degrees]; the
underlying purity interface is the boundary statement
[thm-weil-deligne-purity].
