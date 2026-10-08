+++
id = "lem-sc-rational-function-morphism"
kind = "lemma"
title = "Rational functions define morphisms to $\\mathbf P^1$"
order = 698
uses = ["def-sc-curves", "def-sc-function-field", "lem-sc-regular-dim1-dvr", "lem-sc-smooth-regular"]
+++
Let $C$ be a proper smooth connected curve over
$k$ and $f\in k(C)\setminus k$ ([def-sc-function-field]).
Then $f$ defines a morphism

$$
\pi_f:C\to\mathbf P^1_k
$$

with $\pi_f^*t=f$, where $t$ is the standard coordinate on
$\mathbf P^1$.

## Proof

Write $\mathbf P^1_k=\operatorname{Proj}k[x_0,x_1]$ with
coordinate $t=x_1/x_0$, and cover $C$ by finitely many affine
open subsets $U_\alpha=\operatorname{Spec}A_\alpha$. We first
note that on each $U_\alpha$ one can write $f=a/b$ with
$a,b\in A_\alpha$ and $(a,b)=(1)$ in $A_\alpha$. Indeed, at
every closed point $P\in U_\alpha$ the local ring
$\mathcal O_{C,P}$ is a discrete valuation ring
([lem-sc-smooth-regular],
[lem-sc-regular-dim1-dvr]) with uniformizer $t_P$, and
$f=t_P^{v_P(f)}u_P$ with $u_P$ a unit: if $v_P(f)\geq0$,
then $f=(t_P^{v_P(f)}u_P)/1$ is a representation with
$(a_P,b_P)=(1)$ in $\mathcal O_{C,P}$, and if $v_P(f)<0$,
then $1/f\in\mathcal O_{C,P}$ and $f=1/(1/f)$ is a
representation of the same kind. Starting from any representation
$f=a/b$ and adjoining these finitely many local conditions, one
obtains $a,b$ with
$(a,b)\mathcal O_{C,P}=\mathcal O_{C,P}$ for every closed point
$P$ of $U_\alpha$; then $(a,b)\subseteq A_\alpha$ is
contained in no maximal ideal, hence equals the unit ideal. For
each $\alpha$, the graded $k$-algebra map

$$
k[x_0,x_1]\longrightarrow A_\alpha,\qquad
x_0\longmapsto b_\alpha,\quad x_1\longmapsto a_\alpha,
$$

(with $(a_\alpha,b_\alpha)=(1)$) defines a morphism
$U_\alpha\to\mathbf P^1_k$ sending $t$ to
$a_\alpha/b_\alpha=f|_{U_\alpha}$. On an overlap
$U_\alpha\cap U_\beta$ one has
$a_\alpha b_\beta=a_\beta b_\alpha$ in $k(C)$, so the two
morphisms agree there, and they glue: for two morphisms
$u,v:U_\alpha\cap U_\beta\to\mathbf P^1_k$ agreeing on a dense
open subset, the preimage of the diagonal under
$(u,v):U_\alpha\cap U_\beta\to\mathbf P^1_k\times_k\mathbf P^1_k$ is a closed subset (the diagonal is a
closed immersion by separatedness of $\mathbf P^1_k$) containing
a dense open, hence is the whole scheme. We thus obtain a
morphism $\pi_f:C\to\mathbf P^1_k$ with $\pi_f^*t=f$.
