+++
id = "lem-fd-character-orthogonality"
kind = "lemma"
title = "Orthogonality of additive characters"
order = 2674
lean = ["AddChar.sum_eq_ite"]
uses = ["def-fd-additive-character"]
+++
Let $k_0=\mathbf F_q$, let $\psi_a(x)=\psi(ax)$, and let $c\in\overline{\mathbf Q}_\ell$. Then

$$
\sum_{x\in k_0}c\ \psi_a(x)=\begin{cases}c\cdot q,&\psi_a=1,\\0,&\psi_a\neq1.\end{cases}
$$

In words: a nontrivial additive character sums to zero over the finite
field.

## Proof

If $\psi_a\neq1$, choose $y\in k_0$ with $\psi_a(y)\neq1$; the
translation $x\mapsto x+y$ is a bijection of $k_0$, so

$$
S:=\sum_x c\,\psi_a(x)=\sum_x c\,\psi_a(x+y)=\psi_a(y)S,
$$

hence $(\psi_a(y)-1)S=0$ and $S=0$. If $\psi_a=1$, the sum is
$c\cdot|k_0|=cq$.
