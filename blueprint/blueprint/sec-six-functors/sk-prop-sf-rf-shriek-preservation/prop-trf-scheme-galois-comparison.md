+++
id = "prop-trf-scheme-galois-comparison"
kind = "theorem"
title = "Comparison of scheme and Galois pullbacks"
order = 2076
tags = ["latex:proposition"]
uses = ["def-trf-scheme-frobenius", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-pbc-proetale-site", "def-weil-pbc-scheme-conventions", "lem-trf-absolute-frobenius-site", "prop-trf-frobenius-factorization"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, let $X_0$ be a
finite-type $k_0$-scheme,
put $X=X_0\times_{k_0}k$, and let $A$ be a finite commutative ring
annihilated by an integer invertible in $k$. The $q$-power scheme
Frobenius $\Phi$ and the
geometric-Frobenius automorphism
$g_\gamma$ of [def-trf-scheme-frobenius] induce, on the
small pro-etale site of $X$,
natural isomorphisms of derived categories

$$
\kappa:L\Phi^*\xrightarrow{\ \sim\ }Lg_\gamma^*,
$$

and, for every $m\geq1$, a multiplicative iterate

$$
\kappa^{(m)}:L\Phi^m{}^*\xrightarrow{\ \sim\ }Lg_\gamma^{m*}.
$$

The isomorphisms are compatible with the factorization of
[prop-trf-frobenius-factorization]: scheme Frobenius and geometric
Galois Frobenius differ by a universal homeomorphism, namely the
absolute $q$-power Frobenius. (Source: the comparison between
geometric and arithmetic Frobenius, via the invariance of
the etale site under universal homeomorphisms, is the terminal interface
of the trace-formula chapter.)

## Proof

Write $F_X^{(q)}$ for absolute $q$-power Frobenius.
The canonical trivialization of
[lem-trf-absolute-frobenius-site], iterated $a$ times, gives
$L(F_X^{(q)})^*\simeq\operatorname{id}$.
The factorization [prop-trf-frobenius-factorization] gives
$\Phi=g_\gamma F_X^{(q)}$, where $g_\gamma=g_\sigma^{-1}$
as in [def-trf-scheme-frobenius]. Thus functoriality of pullback
and this specified trivialization give

$$
L\Phi^*=L(F_X^{(q)})^*Lg_\gamma^*
\xrightarrow{\sim}Lg_\gamma^*.
$$

This defines $\kappa$. For $\Phi^m=g_\gamma^mF_X^{(q^m)}$ the
same construction is the multiplicative iterate $\kappa^{(m)}$:
the relative Frobenius maps compose to the corresponding power maps.
The resulting identifications therefore respect both the
factorization and addition of the exponents.

*Recorded in advance* from chapter *The trace formula* of the source.
