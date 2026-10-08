+++
id = "sk-thm-tracetodeterminant"
kind = "section"
title = "Trace-to-determinant identity"
order = 2878
lean = ["TraceDatum.zeta_mul_prod_even_eq_prod_odd"]
uses = ["sk-def-cohfamily", "sk-def-zeta", "sk-prop-logdet", "sk-thm-trace-formula", "sk-thm-trace-transport"]
+++
*Theorem (sketch).*

Let $X_0/\Fq$ be smooth, proper and geometrically connected of pure dimension
$d$, and let $(V_{i,\ell},F_{i,\ell},P_{i,\ell})$ be the family of
[sk-def-cohfamily]. Then

$$
Z(X_0,T)=\prod_{i=0}^{2d}P_{i,\ell}(T)^{(-1)^{i+1}}
\qquad\text{in }\Ql(T)\cap\Ql[[T]] .
$$

## Proof

By [sk-thm-trace-transport] (a) the point counts are alternating traces,
$N_n=\sum_i(-1)^{i}\Tr(F_{i,\ell}^{n}\mid V_{i,\ell})$. Substituting into the
exponential definition of [sk-def-zeta] and exchanging the finite $i$-sum
with the power series,

$$
\log Z(X_0,T)=\sum_{n\ge1}\Bigl(\sum_i(-1)^{i}\Tr(F_{i,\ell}^{n}\mid
V_{i,\ell})\Bigr)\frac{T^{n}}{n}
=\sum_i(-1)^{i}\sum_{n\ge1}\Tr(F_{i,\ell}^{n})\frac{T^{n}}{n}.
$$

By [sk-prop-logdet] the inner series is $-\log P_{i,\ell}(T)$, so
$\log Z=\sum_i(-1)^{i+1}\log P_{i,\ell} =\log\prod_iP_{i,\ell}^{(-1)^{i+1}}$. Exponentiating gives the identity; it
lies in $\Ql(T)$ because the right side is a finite product of rational
functions with constant term $1$, and in $\Ql[[T]]$ because the left side is.

Uses: [sk-def-cohfamily], [sk-def-zeta], [sk-prop-logdet], [sk-thm-trace-formula], [sk-thm-trace-transport]
