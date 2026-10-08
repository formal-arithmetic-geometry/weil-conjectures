+++
id = "lem-zl-noether-normalization-dimension"
kind = "lemma"
title = "The number of Noether coordinates is the Krull dimension"
order = 2649
uses = ["lem-zl-noether-normalization-field", "pqf-lem-going-up", "pqf-lem-incomparability", "pqf-lem-lying-over"]
+++
Let $K$ be a field, $B\neq0$ a finitely generated commutative
$K$-algebra, and $K[T_1,\ldots,T_d]\to B$ an injective $K$-algebra
homomorphism over which $B$ is a finitely generated module (such a
map exists by [lem-zl-noether-normalization-field]). Then
$d=\dim B$, the Krull dimension of $B$; in particular
$\dim B<\infty$.

In particular, if $B$ has Krull dimension one, there is an injective
$K$-algebra homomorphism $K[T]\to B$ making $B$ a finite
$K[T]$-module. This holds in particular over finite fields $K$, and
applies to the coordinate rings of affine charts of the curves over
$\mathbf F_q$ considered in this part.

## Proof

Put $A=K[T_1,\ldots,T_d]$ and regard $A\subseteq B$. A finite
extension is integral, since each element of $B$ acts on the finite
$A$-module $B$ and satisfies the monic characteristic polynomial of that
action (determinant trick). We show $\dim B=\dim A$ and then
$\dim A=d$.

*Step 1 ($\dim B\le\dim A$; incomparability, [pqf-lem-incomparability]).* Let
$\mathfrak q\subsetneq\mathfrak q'$ be primes of $B$; we claim
$\mathfrak q\cap A\neq\mathfrak q'\cap A$. Suppose both contract to
$\mathfrak p$. Then $A/\mathfrak p\hookrightarrow B/\mathfrak q$ is
injective and integral, $B/\mathfrak q$ is a domain, and
$\mathfrak q'/\mathfrak q$ is a nonzero prime contracting to $0$. Pick
$0\neq b\in\mathfrak q'/\mathfrak q$ and a monic equation
$b^n+a_{n-1}b^{n-1}+\cdots+a_0=0$ over $A/\mathfrak p$ of minimal
degree $n$. Then $a_0\neq0$: otherwise
$b(b^{n-1}+\cdots+a_1)=0$ in the domain $B/\mathfrak q$ with $b\ne0$
gives an equation of smaller degree. But
$a_0=-b(b^{n-1}+\cdots+a_1)\in(\mathfrak q'/\mathfrak q)\cap
(A/\mathfrak p)=0$, a contradiction. Hence a strict chain
$\mathfrak q_0\subsetneq\cdots\subsetneq\mathfrak q_r$ in $B$ contracts
to a strict chain of primes of $A$ of the same length, so
$\dim B\le\dim A$.

*Step 2 ($\dim B\ge\dim A$; lifting chains).* Let
$\mathfrak p_0\subsetneq\cdots\subsetneq\mathfrak p_r$ be a chain of
primes of $A$. By lying over [pqf-lem-lying-over] (the map $A\to B$ is
injective and integral) there is a prime $\mathfrak q_0$ of $B$ over
$\mathfrak p_0$, and by going up [pqf-lem-going-up], inductively, primes
$\mathfrak q_0\subseteq\mathfrak q_1\subseteq\cdots\subseteq\mathfrak q_r$
with $\mathfrak q_i\cap A=\mathfrak p_i$. These inclusions are strict
because the contractions are distinct. Hence $\dim B\ge\dim A$.

*Step 3 ($\dim A=d$).* The chain
$0\subsetneq(T_1)\subsetneq(T_1,T_2)\subsetneq\cdots\subsetneq
(T_1,\ldots,T_d)$ of primes of $A$ shows $\dim A\ge d$. That
$\dim K[T_1,\ldots,T_d]\le d$, hence $=d$, is the standard
computation of the dimension of a polynomial ring over a field (for
instance: a strict chain of primes of a finitely generated domain over
$K$ strictly decreases the transcendence degree of the fraction fields
of the successive quotients, and
$\operatorname{Frac}A=K(T_1,\ldots,T_d)$ has transcendence degree $d$;
see Stacks Project, Commutative Algebra, the section on dimension of
finite type algebras over fields).

Combining the three steps, $\dim B=\dim A=d$. For the final
assertion, apply [lem-zl-noether-normalization-field] to $B$ with
$\dim B=1$: it gives some $K[T_1,\ldots,T_d]\to B$ injective and finite,
and the first part forces $d=1$; put $T=T_1$. This is Stacks Project,
Lemma 10.115.4 ([Tag 00OY](https://stacks.math.columbia.edu/tag/00OY)),
together with the equality of dimensions along an integral injective
map ([Tag 00OK](https://stacks.math.columbia.edu/tag/00OK)),
specialized to $\dim B=1$.
