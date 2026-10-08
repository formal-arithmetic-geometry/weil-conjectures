+++
id = "sk-prop-separation"
kind = "section"
title = "Weight separation and the parity factorization"
order = 2898
lean = ["Polynomial.isCoprime_prod_odd_prod_even", "Polynomial.prod_odd_eq_map_and_prod_even_eq_map"]
uses = ["sk-def-cohfamily", "sk-def-roots", "sk-prop-rootpurity", "sk-thm-tracetodeterminant"]
+++
*Proposition (sketch).*

Assume [sk-prop-rootpurity]. Then for $i\ne j$ the polynomials
$P_{i,\ell}$ and $P_{j,\ell}$ are coprime in $\Qlb[T]$, and with the parity
products

$$
N_\ell(T)=\prod_{i\ \text{odd}}P_{i,\ell}(T),\qquad
D_\ell(T)=\prod_{i\ \text{even}}P_{i,\ell}(T)
$$

one has $\gcd(N_\ell,D_\ell)=1$, $N_\ell(0)=D_\ell(0)=1$, and

$$
Z(X_0,T)=\frac{N_\ell(T)}{D_\ell(T)}
\qquad\text{after coefficient extension to }\Ql[[T]] .
$$

More precisely, the ordinary-root multiset of each $P_{i,\ell}$ is exactly the
submultiset of roots of the appropriate parity product whose reciprocal
$\alpha$ satisfies $|\iota(\alpha)|=q^{i/2}$ for the fixed $\iota$.

## Proof

A common ordinary root $\beta$ of $P_{i,\ell}$ and $P_{j,\ell}$ with $i\ne j$
would give reciprocal roots $\alpha=\beta^{-1}$ with $|\iota(\alpha)|=q^{i/2}$
and $=q^{j/2}$ simultaneously, impossible since $q\ne1$. Coprimality of the
parity products follows because a common root would come from some pair
$i\ne j$ of opposite parity; constant terms are $1$ because
$P_{i,\ell}(0)=1=\det(1)$. Evaluating
[sk-thm-tracetodeterminant] with the even exponents
$(-1)^{i+1}=-1$ and odd exponents $+1$ gives
$Z=\prod_{i\ \text{odd}}P_{i,\ell}\big/\prod_{i\ \text{even}}P_{i,\ell} =N_\ell/D_\ell$. The last assertion restates
[sk-prop-rootpurity] root by root, the weights separating the factors
uniquely because $q^{i/2}\ne q^{j/2}$ for $i\ne j$.

Uses: [sk-def-cohfamily], [sk-def-roots], [sk-prop-rootpurity], [sk-thm-tracetodeterminant]
