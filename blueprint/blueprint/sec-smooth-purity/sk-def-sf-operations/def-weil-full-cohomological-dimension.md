+++
id = "def-weil-full-cohomological-dimension"
kind = "definition"
title = "Full cohomological dimension"
order = 1473
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-derived-direct-image", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$, with the finite-torsion coefficient
convention [def-weil-finite-torsion-constructibility]. Let $S$ be a scheme on
which $\ell$ is invertible, let $Y$ and $\overline X$ be finite-type
[def-weil-scheme-morphism-properties] $S$-schemes, and let $p:\overline X\to
Y$ be a proper $S$-morphism. Use finite-torsion $A$-coefficients and the
derived direct image [def-weil-derived-direct-image] $Rp_*$. On the small
pro-etale sites [def-weil-pbc-proetale-site], let $\mathcal H^r$
denote the cohomology-sheaf functor
[def-weil-derived-cohomology-sheaves]. For an integer $c\in\mathbf
Z_{\geq0}$, write $\operatorname{FullCD}(p,A;c)$ if

$$
 \mathcal H^r(Rp_*\mathcal F)=0\qquad(r\in\mathbf Z,\ r>c)
$$

for every sheaf $\mathcal F$ of $A$-modules on $\overline
X_{\mathrm{proet}}$, and, for every object $V\to Y$ of
$Y_{\mathrm{proet}}$, if $p_V:\overline X\times_YV\to V$ is the base change
of $p$, then

$$
 \mathcal H^r\bigl(R(p_V)_*(\mathcal F|_{\overline X\times_YV})\bigr)=0
 \qquad(r\in\mathbf Z,\ r>c).
$$

*Warning.* Because the quantifier ranges over *every* pro-etale sheaf of
$A$-modules, $\operatorname{FullCD}(p,A;c)$ fails in general, even for $p$
proper and smooth of dimension one over an algebraically closed field: for an
elliptic curve $E$ over $\overline{\mathbf F}_p$, $A=\mathbf F_r$ with
$r\neq p$, there is a pro-etale $A$-module sheaf $\mathcal F$ on $E$ with
$H^n(E_{\mathrm{proet}},\mathcal F)\neq0$ for every $n\geq1$
(rem:sf-ambient-counterexample in the six-functors chapter; the sheaf is not
of etale origin). What does hold, with $c=2\dim\overline X$, is the
restriction of the condition to the coefficient sheaves of etale origin,
def-sf-fullcd-class and thm-sf-fullcd-class, and this restricted form is the
only one the blueprint uses.
