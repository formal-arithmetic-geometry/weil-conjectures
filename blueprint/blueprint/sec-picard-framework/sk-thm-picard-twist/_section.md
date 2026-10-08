+++
id = "sk-thm-picard-twist"
kind = "section"
title = "The twist lemma"
order = 754
uses = ["sk-def-av-jacobian", "sk-def-av-pic", "sk-thm-picard-serre-a"]
lean = ["AlgebraicGeometry.Scheme.exists_isInvertible_twist"]
+++
*Theorem (sketch).*

Let $k$ be separably closed, $X$ a smooth projective curve over $k$,
$K/k$ a field extension and $\cL$ a line bundle on $X_K$. Then
there exists a line bundle $\cL_0$ on $X$ such that

$$
h^0\bigl(X_K,\cL\otimes\cL_0|_{X_K}\bigr)=1\qquad\text{and}\qquad
h^1\bigl(X_K,\cL\otimes\cL_0|_{X_K}\bigr)=0 .
$$

## Proof

Choose an ample $\cM$ on $X$. By [sk-thm-picard-serre-b], for $n\gg0$:
$H^q(X_K,\cL\otimes\cM^{\otimes n}|_{X_K})=0$ for $q>0$, and by
[sk-thm-picard-rr] (RR) — applicable, since the integral smooth $X$
has $H^0(X,\cO_X)$ a finite separable extension of the separably
closed $k$, i.e. $H^0(X,\cO_X)=k$, whence $H^0(X_K,\cO_{X_K})=K$ by
flat base change:

$$
\chi\bigl(\cL\otimes\cM^{\otimes n}\bigr)
=\deg_K(\cL)+n\deg_X(\cM)+1-g\ \xrightarrow{\ n\to\infty\ }\infty,
$$

hence $h^0\ge1$. Now use [sk-prop-picard-dense-points]: pick points
$x\in X(k)$ one at a time, at which the chosen non-vanishing
$s\in H^0(\cF)$ does not vanish, and tensor with the ideal sheaf
$\cI_{x_K}=\cO_{X_K}(-x_K)$ (not its inverse, which would add a point
and raise $h^0$); the exact sequence
$0\to\cI_{x_K}\otimes\cF\to\cF\to i_*i^*\cF\to0$ with $s$ shows that
each subtraction lowers $h^0$ by exactly $1$ and preserves $H^1=0$
(the long exact sequence in which $H^1(\cF)$ is the final nonzero term
and $h^0(i_*i^*\cF)=1$, and $H^0(\cF)\to H^0(i_*i^*\cF)$ is onto because
$s(x_K)\ne0$). The induction ends at $h^0=1$; the product of the
$\cI_{x_K}$'s descends to
$\cL_0=\cM^{\otimes n}\otimes\cI_{x_1}\otimes\cdots\otimes\cI_{x_{t-1}}
=\cM^{\otimes n}(-x_1-\cdots-x_{t-1})$ on $X$ (all $x_i\in X(k)$, where
$t=h^0(\cL\otimes\cM^{\otimes n}|_{X_K})$).
