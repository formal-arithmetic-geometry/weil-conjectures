+++
id = "prop-galois-weight-strata-integrality"
kind = "theorem"
title = "Integrality of the normalized stratum polynomials"
order = 2907
tags = ["latex:proposition"]
uses = ["def-weil-numbers", "def-weil-ordinary-reciprocal-roots", "prop-galois-weight-strata"]
+++
In the situation of [prop-galois-weight-strata], for every integer
$i$ with $0\leq i\leq2d$ the normalized stratum polynomial

$$
Q_i(T)=\prod_{\alpha\in R_i}(1-\alpha T)
$$

over the $q$-Weil numbers of weight $i$
lies in $\mathbf Z[T]$.

## Proof

Every element of $R_i$ is a root of the reciprocal polynomial
$A^\#$ or $B^\#$ of [def-weil-ordinary-reciprocal-roots], and
because $A,B\in\mathbf Z[T]$ have constant coefficient one these
reciprocal polynomials are monic with integer coefficients, so their roots
are algebraic integers; every elementary symmetric function of the elements
of $R_i$, counted with multiplicities, is therefore an algebraic integer.
These elementary symmetric functions are, up to sign, the coefficients of

$$
Q_i(T)=\prod_{\alpha\in R_i}(1-\alpha T),
$$

and by [prop-galois-weight-strata] they are fixed by
$\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$, hence rational;
being rational algebraic integers, they lie in $\mathbf Z$.
