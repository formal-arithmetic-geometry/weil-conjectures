+++
id = "lem-zl-euler-product-identity"
kind = "lemma"
title = "Euler-product identity for a Frobenius module"
order = 2393
uses = ["def-zl-frobenius-trace-series", "lem-zl-log-det-identity"]
+++
Let $(V,F)$ be a Frobenius module, as in
the trace-series definition,
and put $N_n=\Tr(F^n\mid V)$ for every $n\geq1$. Then

$$
\exp\left(\sum_{n\geq1}N_n\frac{T^n}{n}\right)
=\det(1-TF\mid V)^{-1}
\quad\text{in }\Qlb[[T]].
$$

## Proof

By [lem-zl-log-det-identity],

$$
\log\det(1-TF\mid V)=-\sum_{n\geq1}N_n\frac{T^n}{n}.
$$

The exponential of a series in $T\Qlb[[T]]$ lies in
$1+T\Qlb[[T]]$, the determinant has constant coefficient $1$ and
hence a multiplicative inverse in $\Qlb[[T]]$, and on these two sets
the formal exponential and the formal logarithm are mutually inverse
bijections. Exponentiating the displayed identity therefore gives

$$
\exp\left(\sum_{n\geq1}N_n\frac{T^n}{n}\right)
=\exp\bigl(-\log\det(1-TF\mid V)\bigr)
=\det(1-TF\mid V)^{-1}.
$$
