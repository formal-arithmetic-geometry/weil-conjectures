+++
id = "lem-sc-deg-principal-zero"
kind = "lemma"
title = "Principal divisors have degree zero"
order = 701
uses = ["def-sc-curves", "def-sc-divisor", "def-sc-function-field", "lem-sc-morphism-from-function", "lem-sc-pullback-degree"]
+++
Let $C$ be a proper smooth connected curve over an
algebraically closed field $k$, and $f\in k(C)^*$. Then

$$
\deg(\operatorname{div}(f))=0.
$$

## Proof

If $f\in k^*$ then $\operatorname{div}(f)=0$. Otherwise
$f\notin k$, and $f$ is transcendental over $k$ (an algebraic
element of $k(C)$ over the algebraically closed field $k$ lies
in $k$). The field $k(C)$ has transcendence degree one over
$k$: for an integral scheme of finite type over a field,
$\dim X=\operatorname{trdeg}_kk(X)$, which is seen by Noether
normalization – an affine integral $k$-algebra $A$ of finite
type admits a finite injective map
$k[x_1,\dots,x_d]\hookrightarrow A$ with $d=\dim A$, whence
$\operatorname{trdeg}_k\operatorname{Frac}(A)=d$ (*reference
for the Noether normalization theorem: Stacks Project, Commutative
Algebra, [Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)*); so $k(C)\neq k$. Let $\pi:=\pi_f:C\to\mathbf P^1_k$
be the morphism of [lem-sc-morphism-from-function], finite flat
of degree $d=[k(C):k(f)]$, with $\pi^*t=f$. Pullback of
divisors is compatible with pullback of functions,
$\operatorname{div}(f)=\operatorname{div}(\pi^*t)=\pi^*\operatorname{div}(t)$:
at a point $P\in C$ with image $Q=\pi(P)$, the valuation $v_P$
on $k(C)$ extends the valuation $v_Q$ on $k(\mathbf P^1)$ with
$v_P(t_Q)=e_P$, where $t_Q$ is a uniformizer of $Q$ and
$e_P:=v_P(t_Q)$ is by definition the coefficient of $P$ in
$\pi^*[Q]$ ([lem-sc-pullback-degree]), so the coefficient of
$P$ in $\operatorname{div}(\pi^*t)$ is
$v_P(t\circ\pi)=v_P(t)=e_Pv_Q(t)$, which is also the coefficient of
$P$ in $\pi^*\operatorname{div}(t)$. Finally,
$\operatorname{div}_{\mathbf P^1}(t)=[0]-[\infty]$ (the function
$t=x_1/x_0$ on $\mathbf P^1_k$ vanishes to order one at
$[0:1]$ and has a pole of order one at $[1:0]$). By
[lem-sc-pullback-degree],

$$
\deg\operatorname{div}(f)=d\cdot\deg([0]-[\infty])=d-d=0.
$$
