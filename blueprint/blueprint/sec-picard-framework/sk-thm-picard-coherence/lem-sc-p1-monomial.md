+++
id = "lem-sc-p1-monomial"
kind = "lemma"
title = "Cohomology of the twists on $\\mathbf P^1_k$"
order = 639
uses = ["def-sc-kahler-differentials", "def-sc-p1-standard", "lem-pc-projective-space-canonical", "lem-sc-canonical-sheaf", "lem-sc-cech-spectral", "lem-sc-p1-twist-exists", "lem-sc-p1-twist-sections", "pqf-lem-affine-vanishing"]
+++
Let $k$ be an algebraically closed field. With the standard cover
and twists of [def-sc-p1-standard], for every $d\in\mathbf Z$:

1. **(i)** $H^0(\mathbf P^1_k,\mathcal O(d))$ is the space of
sections corresponding to the homogeneous polynomials of degree
$d$ in $k[x_0,x_1]$ (the monomial $x_0^ax_1^b$, $a+b=d$,
corresponding to the pair $(t^b,s^a)$), hence has dimension $d+1$
for $d\geq0$ and is zero for $d<0$;
1. **(ii)** $H^1(\mathbf P^1_k,\mathcal O(d))=0$ for $d\geq-1$;
for $d\leq-2$, $H^1(\mathbf P^1_k,\mathcal O(d))$ has the basis
$$
\bigl[t^{d+1}\bigr],\dots,\bigl[t^{-1}\bigr]
$$
of the classes of the monomials $t^j\in \Gamma(U_{01},\mathcal O(d))=k[t,t^{-1}]$, and has dimension
$-d-1$; in particular
$H^1(\mathbf P^1_k,\mathcal O(-2))\cong k$, with basis
$[t^{-1}]$;
1. **(iii)** $\omega_{\mathbf P^1}:=\Omega^1_{\mathbf P^1_k/k}$
([def-sc-kahler-differentials]) is a line bundle
([lem-sc-canonical-sheaf]), and
$\omega_{\mathbf P^1}\cong\mathcal O(-2)$: with the trivializations
$dt$ on $U_0$ and $ds$ on $U_1$ one has $ds=-s^{2}dt$,
equivalently $dt=-t^{2}ds$, and this transition function $-t^{2}$
is the transition function $t^{2}$ of $\mathcal O(-2)$ up to the
unit $-1$.

## Proof

By [lem-sc-cech-spectral] applied to the Zariski covering
$\mathfrak U=\{U_0,U_1\}$ of [def-sc-p1-standard], the
$E_2$-terms are
$E_2^{p,q}=\check H^p(\mathfrak U,\underline H^q(\mathcal O(d)))$.
The cohomology presheaves $\underline H^q(\mathcal O(d))$ vanish
for $q>0$ on the affine members $U_0,U_1,U_{01}$ because
$\mathcal O(d)$ is quasi-coherent ([pqf-lem-affine-vanishing]),
and $\check H^p=0$ for $p\geq2$ because the covering has two
members. Here $\mathcal O(d)$ is the invertible module of
[lem-sc-p1-twist-exists], whose sections over
$U_0,U_1,U_{01}$ are those described by
[lem-sc-p1-twist-sections]; hence
$H^0(\mathbf P^1_k,\mathcal O(d))$ and
$H^1(\mathbf P^1_k,\mathcal O(d))$ are the kernel and the cokernel
of

$$
\delta:k[t]\times k[s]\longrightarrow k[t,t^{-1}],
\qquad
(p,q)\longmapsto p-t^{d}q(1/t).
$$

For (i): $(p,q)\in\ker\delta$ means $p=t^dq(1/t)$. If $d\geq0$,
this says that $p$ is a polynomial of degree at most $d$: if
$q(s)=\sum_i c_is^{i}$, then $p(t)=\sum_ic_it^{d-i}$, and
conversely, for $p=\sum_{j=0}^{d}a_jt^{j}$, take
$q(s)=\sum_{j=0}^{d}a_js^{d-j}$. The monomial $x_0^ax_1^b$,
$a+b=d$, corresponds to $(t^b,s^a)$, so the kernel has dimension
$d+1$. If $d<0$, every exponent of $t^dq(1/t)$ is at most
$d<0$, and as $p$ is a polynomial this forces $p=q=0$.
For (ii): the image of $\delta$ is spanned by $t^{j}$ with
$j\geq0$ (the elements $(t^{j},0)$) and by $t^dq(1/t)$ with
$q\in k[s]$, i.e. by $t^{j}$ with $j\leq d$; so for $d\geq-1$
the image is all of $k[t,t^{-1}]$ and $H^1=0$, while for
$d\leq-2$ the quotient has the basis of classes
$[t^{d+1}],\dots,[t^{-1}]$, of dimension $-d-1$.
For (iii): $\omega_{\mathbf P^1}$ is a line bundle by
[lem-sc-canonical-sheaf] applied to the smooth curve
$\mathbf P^1_k$; on $U_0$ it has the generator $dt$, on $U_1$
the generator $ds$, and since $s=1/t$,
$ds=-s^{2}dt$, i.e. $dt=-t^{2}ds$, so that the transition
function $-t^{2}$ differs from the transition function $t^{2}$ of
$\mathcal O(-2)$ by the unit $-1$, whence
$\omega_{\mathbf P^1}\cong\mathcal O(-2)$.
(This is the case $n=1$, $A=k$ of [lem-pc-projective-space-canonical],
which gives $\omega_{\mathbf P^n}\cong\mathcal O(-n-1)$ in general.)
