+++
id = "lem-wf-engel-matrix"
kind = "lemma"
title = "Engel's matrix lemma"
order = 2469
+++
Let $M\ne0$ be a finite-dimensional vector space over $\Qlb$, and let
$\mathfrak n\subseteq\operatorname{End}(M)$ be a
finite-dimensional Lie algebra over $\Qlb$, and suppose that every
$X\in\mathfrak n$ is a nilpotent endomorphism. Then some nonzero
vector of $M$ is killed by every element of $\mathfrak n$.
Consequently there is a basis in which every element of
$\mathfrak n$ is strictly upper triangular, and $\mathfrak n$ is
nilpotent, hence solvable.

## Proof

We first prove the common-kernel assertion by induction on
$\dim\mathfrak n$. If $\mathfrak n=0$, every nonzero vector works.
Otherwise choose a maximal proper Lie subalgebra
$\mathfrak a\subsetneq\mathfrak n$. If $X^r=0$, then

$$
(\operatorname{ad}X)^m(Y)
=\sum_{i=0}^{m}(-1)^i\binom mi X^{m-i}YX^i,
$$

so $(\operatorname{ad}X)^{2r-1}=0$. Thus every member of
$\mathfrak a$ acts nilpotently on $\mathfrak n/\mathfrak a$.
Induction applied to this action gives
$Y\notin\mathfrak a$ with
$[\mathfrak a,Y]\subseteq\mathfrak a$. Hence the normalizer of
$\mathfrak a$ strictly contains $\mathfrak a$; maximality makes
that normalizer all of $\mathfrak n$. Thus $\mathfrak a$ is an
ideal. Moreover $\mathfrak n/\mathfrak a$ is one-dimensional:
otherwise the inverse image of a one-dimensional subalgebra of the
quotient would lie strictly between $\mathfrak a$ and
$\mathfrak n$.

Induction applied to $\mathfrak a$ acting on $M$ shows that

$$
M^{\mathfrak a}=\{v:Av=0\text{ for all }A\in\mathfrak a\}
$$

is nonzero. It is $\mathfrak n$-stable because $\mathfrak a$ is
an ideal. If $X$ maps to a basis of
$\mathfrak n/\mathfrak a$, then the nilpotent operator
$X|_{M^{\mathfrak a}}$ has nonzero kernel. Any nonzero vector in
that kernel is killed by $\mathfrak a$ and by $X$, hence by all of
$\mathfrak n$.

Choose such a vector as the first basis vector and apply the same
argument to the induced action on its quotient. Induction on
$\dim M$ gives simultaneous strict upper triangularity. A bracket
of sufficiently many strictly upper-triangular matrices is zero, so
the lower central series terminates; this is nilpotence and therefore
solvability.
