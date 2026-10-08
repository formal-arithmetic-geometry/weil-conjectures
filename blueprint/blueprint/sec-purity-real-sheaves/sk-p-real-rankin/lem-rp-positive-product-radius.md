+++
id = "lem-rp-positive-product-radius"
kind = "lemma"
title = "Positive products and radii of convergence"
order = 2662
uses = ["d-real-series"]
+++
Let $\{f_j(t)\}_{j\in J}$ be a locally finite family of series

$$
f_j(t)=1+\sum_{n\ge1}a_{j,n}t^n\in1+t\mathbf R_{\ge0}[[t]],
$$

meaning that each coefficient of the formal product
$F(t):=\prod_{j\in J}f_j(t)=\sum_{n\ge0}A_nt^n$ receives contributions
from only finitely many factors. If this formal series is the Taylor
series at $0$ of a function holomorphic on $|t|<R$, then every
$f_j$ has radius of convergence at least $R$ (in the sense of [d-real-series]). In particular, if
$f_j=P_j(t)^{-1}$ with $P_j(0)=1$ a polynomial, then $P_j$ has no
zero in $|t|<R$.

## Proof

Nonnegativity and the constant terms $1$ give the coefficientwise
inequality $0\le a_{j,n}\le A_n$. Fix $0<r<R$. Cauchy's estimate for
the holomorphic function represented by $F$ gives a constant $C_r$ with
$|A_n|\le C_r r^{-n}$ for all $n$. Hence
$\limsup_n a_{j,n}^{1/n}\le r^{-1}$, so the radius of $f_j$ is at least
$r$. Letting $r\uparrow R$ proves the first assertion. For a reciprocal
polynomial, a zero of $P_j$ would be a pole of its reciprocal power series,
so no such zero can lie in the open disc.
