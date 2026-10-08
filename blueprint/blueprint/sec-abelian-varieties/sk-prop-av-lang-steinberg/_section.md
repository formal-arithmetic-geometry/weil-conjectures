+++
id = "sk-prop-av-lang-steinberg"
kind = "section"
title = "Lang–Steinberg for $p$-linear maps"
lean = ["LinearMap.Frobenius.surjective_sub_id"]
order = 564
uses = ["sk-def-av", "sk-prop-av-fixed-points"]
+++
*Proposition (sketch).*

Let $k$ be algebraically closed of characteristic $p>0$, $V$ a
finite-dimensional $k$-vector space and $F:V\to V$ $p$-linear. Then
$F-1:V\to V$ is surjective.

## Proof

The skew ring $k[\tau]$ is a left Euclidean domain (the leading
coefficient $c\,a^{p^m}$ of $\tau^mg$ can always be cancelled because
$k$ is algebraically closed), so $V$, made a $k[\tau]$-module by
$\tau\cdot v=F(v)$, decomposes into cyclic blocks
$k[\tau]v\cong k[\tau]/k[\tau]p(\tau)$ with
$p(\tau)=\tau^m-\sum_{i=1}^ma_i\tau^{i-1}$, $m\le\dim_kV$. In the
basis $v,Fv,\dots,F^{m-1}v$ the map reads
$F(x_1,\dots,x_m)=(a_1x_m^p,x_1^p+a_2x_m^p,\dots,x_{m-1}^p+a_mx_m^p)$.
The first $m-1$ equations of $F(x)-x=w$ express each $x_i$ as a
polynomial in $x_m$ (by induction, using $(u+v)^p=u^p+v^p$):

$$
x_i=\sum_{k=1}^{i}a_k^{p^{\,i-k}}x_m^{p^{\,i-k+1}}
-\sum_{k=1}^{i}w_k^{p^{\,i-k}},
$$

and substitution into the last equation gives a polynomial equation
$\varphi(x_m)=0$ whose linear coefficient is $1$, hence a nonzero
polynomial of degree $\le p^m$ with a root in the algebraically closed
field $k$. Back-substitution produces $x_i$ with $F(x)-x=w$.

Uses: [sk-def-av], [sk-prop-av-fixed-points]
