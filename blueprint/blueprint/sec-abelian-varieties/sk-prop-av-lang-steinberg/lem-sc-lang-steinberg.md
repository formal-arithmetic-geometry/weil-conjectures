+++
id = "lem-sc-lang-steinberg"
kind = "lemma"
title = "Lang–Steinberg for vector spaces"
lean = ["LinearMap.Frobenius.surjective_sub_id"]
order = 565
+++
Let $k$ be an algebraically closed field of characteristic
$p>0$, $V$ a finite-dimensional $k$-vector space and
$F:V\to V$ a $p$-linear endomorphism. Then

$$
F-1:V\longrightarrow V
$$

is surjective.

## Proof

*Step 1: the skew polynomial ring.* Let $k[\tau]$ be the
skew polynomial ring with $\tau\lambda=\lambda^p\tau$ for
$\lambda\in k$. It is a left Euclidean domain: for
$f,g\in k[\tau]$ with $g\neq0$ and $\deg f\geq\deg g$, write
$f=c\tau^{\deg f-\deg g}g+f'$ where $c\in k$ is chosen so that
the leading terms cancel (the leading coefficient of
$\tau^mg$ with $g$ of leading term $a\tau^n$ is
$c\,a^{p^m}$, and every element of the algebraically closed field
$k$ has a $p^m$-th root, so $c$ exists) and $f'$ has smaller
degree. Hence every finitely generated torsion $k[\tau]$-module
is a direct sum of cyclic modules $k[\tau]/k[\tau]p(\tau)$
(the structure theorem for finitely generated torsion modules over
a principal ideal domain: *reference: Stacks Project, More on
Algebra, Lemma 15.126.9, [Tag 0ASV](https://stacks.math.columbia.edu/tag/0ASV); its proof reduces first to the
torsion case – automatic here, since for every nonzero
$m\in V$ the elements $m,\tau m,\tau^2m,\dots$ lie in the
finite-dimensional $k$-vector space $k[\tau]m\subseteq V$, so
the first $k$-linear dependence
$\tau^dm=\sum_{i=1}^da_i\tau^{i-1}m$ yields the annihilator
$p(\tau)=\tau^d-\sum_{i=1}^da_i\tau^{i-1}$ – and the induction
of loc. cit. splits off cyclic direct summands using only the
division algorithm, which carries over verbatim to the left
Euclidean ring $k[\tau]$ because every step involves only the
division algorithm and left ideals*).

*Step 2: reduction to blocks.* The $p$-linear endomorphism
$F$ makes $V$ a $k[\tau]$-module via $\tau\cdot v:=F(v)$
(indeed $\tau\cdot(\lambda v)=F(\lambda v)=\lambda^pF(v)= \tau\lambda\cdot v$). By Step 1, $V$ decomposes into cyclic
blocks $k[\tau]v\cong k[\tau]/k[\tau]p(\tau)$ with
$p(\tau)=\tau^m-\sum_{i=1}^ma_i\tau^{i-1}$, $m\leq\dim_kV$. In
the basis $v,F(v),\dots,F^{m-1}(v)$ of the block, with coordinates
$(x_1,\dots,x_m)$ (so that the element is
$x_1v+x_2F(v)+\cdots+x_mF^{m-1}(v)$), the relation
$p(\tau)v=0$ gives
$F^m(v)=\sum_ia_iF^{i-1}(v)$, and therefore

$$
F(x_1,\dots,x_m)=\bigl(a_1x_m^p,\,
x_1^p+a_2x_m^p,\,x_2^p+a_3x_m^p,\,\dots,\,
x_{m-1}^p+a_mx_m^p\bigr),
$$

because $F\bigl(\sum_ix_iF^{i-1}(v)\bigr)=\sum_ix_i^pF^i(v)$
with $F^m(v)$ expanded by the relation.

*Step 3: solving on each block.* The equation
$F(x)-x=w$ on a block reads

$$
a_1x_m^p-x_1=w_1,\qquad
x_{i-1}^p+a_ix_m^p-x_i=w_i\quad(2\leq i\leq m).
$$

The first $m-1$ equations express
the $x_i$ in terms of $x_m$ by

$$
x_1=a_1x_m^p-w_1,\qquad
x_i=x_{i-1}^p+a_ix_m^p-w_i\quad(2\leq i\leq m),
$$

so each $x_i$ is a polynomial in $x_m$ with coefficients in
$k$: explicitly

$$
x_i=\sum_{k=1}^{i}a_k^{p^{\,i-k}}x_m^{p^{\,i-k+1}}
-\sum_{k=1}^{i}w_k^{p^{\,i-k}}
\qquad(1\leq i\leq m),
$$

as one checks by induction on $i$ using $(u+v)^p=u^p+v^p$
in characteristic $p$. Substituting into the last equation
($i=m$) gives

$$
\varphi(x_m):=x_m-\sum_{k=1}^{m}a_k^{p^{\,m-k}}x_m^{p^{\,m-k+1}}
+\sum_{k=1}^{m-1}w_k^{p^{\,m-k}}+w_m=0,
$$

a polynomial equation in the single variable $x_m$ with
coefficients in $k$: the linear coefficient of $\varphi$ is
$1$, so $\varphi$ is a nonzero polynomial of degree at most
$p^m$, which has a root because $k$ is algebraically
closed. The remaining coordinates are then recovered by
back-substitution. Hence $F-1:V\to V$ is surjective.
