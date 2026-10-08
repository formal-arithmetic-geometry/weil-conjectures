+++
id = "lem-ag-faithful-semisimple-lie-central-radical"
kind = "lemma"
title = "A faithful semisimple Lie representation forces a central radical"
order = 2474
uses = ["def-wf-lie-radical-centre", "lem-ag-central-radical-quotient", "lem-wf-solvable-common-eigenvector", "lem-wf-sum-of-solvable-ideals"]
+++
Let $L$ be a finite-dimensional Lie algebra over
$\overline{\mathbf Q}_\ell$, and let $\rho:L\to\operatorname{End}(V)$ be
a Lie representation on a finite-dimensional vector space $V$, i.e. a
linear map with $\rho([x,y])=\rho(x)\rho(y)-\rho(y)\rho(x)$. Assume that
$\rho$ is faithful ($\ker\rho=0$) and semisimple: $V=\bigoplus_iM_i$ is a
direct sum of nonzero $\rho(L)$-stable subspaces $M_i$, each having no
$\rho(L)$-stable subspaces other than $0$ and $M_i$. Then, in the notation
of [def-wf-lie-radical-centre], $L$ has central radical and

$$
\operatorname{rad}L=Z(L),\qquad L=Z(L)+[L,L],
$$

where the plus sign denotes a sum of subspaces.

## Proof

Put $\mathfrak r=\operatorname{rad}L$, the sum of all solvable ideals
of [def-wf-lie-radical-centre]. As $L$ is finite-dimensional, this is
a finite sum of solvable ideals, so it is a solvable ideal by
[lem-wf-sum-of-solvable-ideals] and induction on the number of summands.
Write $xv$ for $\rho(x)v$. Fix one
summand $M=M_i$. The solvable Lie algebra $\mathfrak r$ acts on
$M\ne0$ through $\rho$, so [lem-wf-solvable-common-eigenvector] gives
a linear form $\lambda:\mathfrak r\to\overline{\mathbf Q}_\ell$ for which

$$
M_\lambda=\{v\in M:av=\lambda(a)v\text{ for all }a\in\mathfrak r\}
$$

is nonzero.

We show that $M_\lambda$ is $\rho(L)$-stable. Let $x\in L$ and
$0\ne v\in M_\lambda$, and put $U_j=\operatorname{span}\{v,xv,\ldots,
x^{j-1}v\}$ and $U=\bigcup_jU_j$, a finite-dimensional $x$-stable
subspace of $M$. From

$$
ax^jv=x\,(ax^{j-1}v)+[a,x]x^{j-1}v
$$

and $[a,x]\in\mathfrak r$ (as $\mathfrak r$ is an ideal), induction on
$j$ shows that for every $a\in\mathfrak r$,

$$
ax^jv\equiv\lambda(a)x^jv\pmod{U_j}.
$$

Hence $U$ is $\mathfrak r$-stable and each $a\in\mathfrak r$ acts on $U$
by an upper-triangular matrix, in the ordered basis extracted from
$v,xv,x^2v,\ldots$, with constant diagonal entry $\lambda(a)$. For
$a\in\mathfrak r$, the element $[x,a]\in\mathfrak r$ acts on $U$ as the
commutator of the two endomorphisms $x|_U$ and $a|_U$, so

$$
0=\operatorname{tr}_U\bigl([x|_U,a|_U]\bigr)=(\dim U)\,\lambda([x,a]),
$$

and characteristic zero gives $\lambda([x,a])=0$. Consequently

$$
a(xv)=x(av)+[a,x]v=\lambda(a)\,xv+\lambda([a,x])\,v=\lambda(a)\,xv,
$$

so $xv\in M_\lambda$. Thus $M_\lambda$ is a nonzero
$\rho(L)$-stable subspace of $M$, and the simplicity of $M$ gives
$M_\lambda=M$. Moreover the computation shows that every $[x,a]$ with
$x\in L$, $a\in\mathfrak r$ acts on $M$ by the scalar
$\lambda([x,a])=0$.

Applying this to every summand $M_i$, the subspace $[L,\mathfrak r]$ acts
as zero on $V=\bigoplus_iM_i$. Faithfulness of $\rho$ gives
$[L,\mathfrak r]=0$, that is, $\mathfrak r\subseteq Z(L)$. Conversely,
$Z(L)$ is an ideal with $[Z(L),Z(L)]=0$, so it is solvable and is
contained in the sum of all solvable ideals: $Z(L)\subseteq\mathfrak r$.
Hence $\operatorname{rad}L=Z(L)$. The radical being central,
[lem-ag-central-radical-quotient] gives $L=Z(L)+[L,L]$.
