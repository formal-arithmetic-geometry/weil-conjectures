+++
id = "lem-wf-affine-dimension-drop"
kind = "lemma"
title = "Proper closed subsets have strictly smaller dimension"
order = 2485
+++
Let $X$ be an irreducible affine variety over a field $k$, with
coordinate algebra $k[X]$ (finitely generated and reduced). Then $k[X]$
is a domain, and every closed subset $Y\subsetneq X$ satisfies
$\dim Y\le\dim X-1$ (with the convention $\dim\varnothing=-1$), where
dimension is the supremum of lengths of strict chains of prime ideals of
the coordinate algebra.

## Proof

*Domain.* The closure of a point $\mathfrak p$ of
$X=\operatorname{Spec}k[X]$ is $V(\mathfrak p)$, and $X=\bigcup V(\mathfrak p)$
over the minimal primes. If $ab=0$ in $k[X]$, then every prime contains
$a$ or $b$, so $X=V(a)\cup V(b)$; by irreducibility $X=V(a)$, say, so
$a$ lies in every prime ideal, hence in the nilradical, which is $0$
because $k[X]$ is reduced. Thus $k[X]$ is a domain ($X$ is nonempty, so
$k[X]\neq0$).

*Finiteness of the dimension.* By Noether normalization there is a
finite injective $k$-algebra map $k[t_1,\ldots,t_d]\to k[X]$, and for
an integral extension the Krull dimensions agree (lying over, going up
and incomparability); the polynomial ring has dimension $d$. So
$\dim X=d$ is a finite integer.

*Strict drop.* Write $Y=V(I)$ with $I$ radical, so that $k[Y]=k[X]/I$.
If $Y=\varnothing$ there is nothing to prove, as $\dim X\ge0$. Otherwise
$I$ is a proper ideal, and $I\neq0$: radical ideals correspond
bijectively to closed subsets and $V(0)=X\neq Y$. A strict chain
$\mathfrak q_0\subsetneq\cdots\subsetneq\mathfrak q_r$ of primes of
$k[X]/I$ pulls back to a strict chain of primes of $k[X]$ containing
$I$; all of them are nonzero, so prepending the prime $(0)$ of the
domain $k[X]$ yields a strict chain of length $r+1$. Hence
$\dim Y+1\le\dim X$, and $\dim Y$ is finite since $\dim X$ is.
