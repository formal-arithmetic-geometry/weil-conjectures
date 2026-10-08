+++
id = "def-sc-divisor"
kind = "definition"
title = "Divisors, principal divisors, class group"
order = 444
uses = ["def-sc-curves", "def-sc-function-field"]
+++
Let $C$ be a connected curve over $k$. A
*divisor* on $C$ is a finite formal sum
$D=\sum_Pn_P[P]$ of closed points $P$ of $C$ with integer
coefficients; $\operatorname{Div}(C)$ is the free abelian group on
the closed points of $C$. For $f\in k(C)^*$
([def-sc-function-field]), its *divisor* is

$$
\operatorname{div}(f)=\sum_P v_P(f)\,[P],
$$

where $v_P$ is the normalized valuation of the local ring
$\mathcal O_{C,P}$; such divisors are *principal*. That
$\mathcal O_{C,P}$ is a discrete valuation ring when $C$ is
smooth, so that $v_P$ is defined, is
[lem-sc-smooth-regular] together with
[lem-sc-regular-dim1-dvr], and it is not part of the
definition.
The *divisor class group* is

$$
\operatorname{Cl}(C):=\operatorname{Div}(C)/\{\operatorname{div}(f):f\in k(C)^*\}.
$$

For $D=\sum n_P[P]$ the associated sub-$\mathcal O_C$-module of
the constant sheaf $k(C)$ is

$$
\mathcal O_C(D)(U):=\{f\in k(C):\operatorname{div}(f)|_U+D|_U\geq0\};
$$

that it is invertible for $C$ smooth, i.e. that
$D\mapsto[\mathcal O_C(D)]$ identifies
$\operatorname{Cl}(C)$ with $\operatorname{Pic}(C)$, is
recorded with the other properties of this construction, and it is not part of the
definition. The
*degree* of $D$ is

$$
\deg D:=\sum_Pn_P.
$$

(For reducible $C$ all objects above are defined componentwise.)
