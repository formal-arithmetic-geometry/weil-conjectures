+++
id = "prop-weil-reciprocal-roots-eigenvalues"
kind = "theorem"
title = "Reciprocal roots as eigenvalues"
order = 2896
tags = ["latex:proposition"]
uses = ["def-weil-frobenius-detailed", "def-weil-ordinary-reciprocal-roots", "def-weil-smooth-proper-cohomological-family"]
+++
For $P_{i,\ell}$ of
[def-weil-ordinary-reciprocal-roots], the
reciprocal roots are
exactly the eigenvalues of $F_{i,\ell}$ after scalar extension to
$\Qlb$ (the determinant identity $\det(1-TF)= \prod_j(1-\alpha_jT)$ over the algebraically closed field).

## Proof

After scalar extension to $\Qlb$, the operator $F_{i,\ell}$ on
$V_{i,\ell}\otimes_{\Ql}\Qlb$ has eigenvalues
$\lambda_1,\ldots,\lambda_m$ with $m=\dim_{\Ql}V_{i,\ell}$, counted
with algebraic multiplicity, and over the algebraically closed field

$$
\det(1-TF_{i,\ell}\mid V_{i,\ell})
=\prod_{j=1}^{m}(1-\lambda_jT).
$$

By [def-weil-ordinary-reciprocal-roots], the same factorization
displays the reciprocal roots of $P_{i,\ell}$ with algebraic
multiplicity, so the reciprocal roots are precisely the $\lambda_j$,
i.e. exactly the eigenvalues of $F_{i,\ell}$ in $\Qlb$.
