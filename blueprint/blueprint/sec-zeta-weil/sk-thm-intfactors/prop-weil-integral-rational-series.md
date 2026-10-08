+++
id = "prop-weil-integral-rational-series"
kind = "theorem"
title = "Normalized integral fraction for an integral rational series"
order = 2902
tags = ["latex:proposition"]
uses = ["def-weil-normalized-integral-fraction", "lem-weil-finite-coordinate-detection", "prop-weil-rationality-criterion"]
+++
Let $Z(T)\in1+T\mathbf Z[[T]]$ be rational over $\mathbf Q$.
Then $Z$ has a unique
normalized reduced
integral presentation: there are unique $A,B\in\mathbf Z[T]$
such that $A(0)=B(0)=1$, $\gcd(A,B)=1$ in $\mathbf Q[T]$,
and $BZ=A$.

## Proof

Write $Z=\sum_{n\geq0}z_nT^n$ and
$R_j=(z_{j+s})_{s\geq0}$. By
[prop-weil-rationality-criterion], their rational span $V$
is finite-dimensional. Left shift $S(v)_n=v_{n+1}$ preserves $V$,
since $S(R_j)=R_{j+1}$.
Put $L=V\cap\mathbf Z^{\mathbf Z_{\geq0}}$.
This subgroup contains every $R_j$, spans $V$ over $\mathbf Q$,
and is preserved by $S$.

Choose a finite coordinate set $J$ using
[lem-weil-finite-coordinate-detection]. Evaluation embeds $L$
in $\mathbf Z^J$. A subgroup of $\mathbf Z^r$ is finite free:
induct on $r$, project to the last coordinate, and write the image
as $d\mathbf Z$. If the image is zero, apply induction in
$\mathbf Z^{r-1}$. Otherwise choose one lift of $d$; it splits
off a copy of $\mathbf Z$, with kernel a subgroup of
$\mathbf Z^{r-1}$. This proves the assertion and supplies a finite
basis of $L$.

In this basis $S|_L$ has an integer matrix $M$, $R_0$ has an
integer coordinate column $v$, and evaluation at coordinate zero
has an integer row $e$. Thus

$$
z_n=eM^nv,\qquad
Z(T)=e(I-TM)^{-1}v
=\frac{e\,\operatorname{adj}(I-TM)v}{\det(I-TM)}.
$$

The inverse identity is a formal power series identity:
$(I-TM)\sum_{n\geq0}T^nM^n=I$ coefficient by coefficient.
Let $A_0=e\,\operatorname{adj}(I-TM)v$ and
$B_0=\det(I-TM)$. They are integer polynomials and
$B_0(0)=1$, $A_0(0)=ev=z_0=1$.

Choose a primitive integer polynomial $G$ representing the greatest
common divisor of $A_0,B_0$ over $\mathbf Q[T]$.
Gauss' lemma says that a primitive integer polynomial dividing an
integer polynomial over $\mathbf Q[T]$ already divides it over
$\mathbf Z[T]$. Hence $A_0=GA$ and $B_0=GB$ with integral
quotients. The equality $1=B_0(0)=G(0)B(0)$ forces
$G(0)=\pm1$. Choose its sign so that $G(0)=1$; then
$A(0)=B(0)=1$, and the two quotients are coprime.
They give the presentation of [def-weil-normalized-integral-fraction].

If $A/B=A'/B'$ are two such reduced fractions, $AB'=A'B$.
Coprimality implies $B\mid B'$ and $B'\mid B$ in
$\mathbf Q[T]$, so $B'=cB$ for $c\in\mathbf Q^\times$.
Their constant terms force $c=1$, and then $A'=A$.
