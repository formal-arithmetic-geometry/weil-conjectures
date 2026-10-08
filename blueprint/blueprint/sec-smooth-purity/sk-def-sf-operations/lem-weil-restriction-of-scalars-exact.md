+++
id = "lem-weil-restriction-of-scalars-exact"
kind = "lemma"
title = "Exactness of restriction of scalars"
order = 1456
uses = ["def-weil-completed-integral-coefficients", "def-weil-pbc-proetale-site"]
+++
Fix a prime $\ell\neq p$, a finite extension $E/\Ql$ with valuation ring
$\mathcal O_E$ and uniformizer $\varpi_E$, a scheme $Y$, and an integer
$n\in\mathbf Z_{\geq1}$, and let $\widehat{\mathcal
O}_{E,Y}\twoheadrightarrow(A_{E,n})_Y$ be the reduction of the completed
coefficient sheaf [def-weil-completed-integral-coefficients]. Then the
restriction of scalars $\operatorname{Res}_n$ is an exact functor

$$
 \operatorname{Res}_n:
 \Sh(Y_{\mathrm{proet}},A_{E,n})
 \longrightarrow\Sh(Y_{\mathrm{proet}},\mathcal O_E)
$$

between the categories of sheaves on the small pro-etale site
[def-weil-pbc-proetale-site].

## Proof

Kernels, images and cokernels of morphisms of sheaves of modules on the small
pro-etale site [def-weil-pbc-proetale-site] are formed termwise on
the underlying sheaves of abelian groups, and $\operatorname{Res}_n$ of
[def-weil-completed-integral-coefficients] is the identity on underlying
sheaves of abelian groups: the $\widehat{\mathcal O}_{E,Y}$-module structure
it uses is the one induced by the ring surjection $\widehat{\mathcal
O}_{E,Y}\twoheadrightarrow(A_{E,n})_Y$. A short exact sequence of
$A_{E,n}$-modules therefore remains short exact after restriction of scalars,
which is the exactness asserted.
