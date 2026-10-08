+++
id = "lem-zl-log-det-identity"
kind = "lemma"
title = "Logarithm of the Frobenius determinant"
order = 2392
uses = ["def-zl-frobenius-trace-series", "p-linear-triangular"]
+++
Let $(V,F)$ be a Frobenius module, as in
the trace-series definition.
Then, as formal power series in $\Qlb[[T]]$,

$$
\log\det(1-TF\mid V)
=-\sum_{n\geq1}\Tr(F^n\mid V)\frac{T^n}{n}
=-\operatorname{tr}_F(T).
$$

No semisimplicity assumption is imposed on $F$.

## Proof

The field $\Qlb$ is algebraically closed, so by [p-linear-triangular] choose a basis of $V$ in
which the matrix of $F$ is upper triangular; let

$$
\lambda=(\lambda_1,\ldots,\lambda_m),\qquad m=\dim_{\Qlb}V,
$$

be its diagonal entries, i.e. the eigenvalues of $F$ with algebraic
multiplicity. The matrix of $F^n$ is upper triangular with diagonal
$(\lambda_1^n,\ldots,\lambda_m^n)$, so

$$
\Tr(F^n\mid V)=\sum_{j=1}^{m}\lambda_j^n,
$$

and the matrix of $1-TF$ is upper triangular with diagonal
$(1-\lambda_1T,\ldots,1-\lambda_mT)$, so

$$
\det(1-TF\mid V)=\prod_{j=1}^{m}(1-\lambda_jT).
$$

Every factor lies in $1+T\Qlb[[T]]$, where the formal logarithm is a
homomorphism for finite products: for
$A,B\in1+T\Qlb[[T]]$ the derivative of $\log(AB)$ is
$(AB)'/(AB)=A'/A+B'/B$, the derivative of $\log A+\log B$, and both
sides have constant term $0$. For a single factor, the definition of
the formal logarithm gives

$$
\log(1-\lambda T)=-\sum_{n\geq1}\frac{\lambda^nT^n}{n}.
$$

Summing over $j=1,\ldots,m$, interchanging the two finite index ranges,

$$
\log\det(1-TF\mid V)
=-\sum_{n\geq1}\left(\sum_{j=1}^{m}\lambda_j^n\right)\frac{T^n}{n}
=-\sum_{n\geq1}\Tr(F^n\mid V)\frac{T^n}{n},
$$

which is the negative of the trace series of
[def-zl-frobenius-trace-series].
