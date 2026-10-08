+++
id = "lemma-weil-pbc-finite-refinement-etale-cover"
kind = "lemma"
title = "Finite refinement of a surjective etale morphism"
order = 1074
uses = ["def-weil-pbc-etale-site", "def-weil-pbc-scheme-conventions"]
+++
Let $U\to T$ be surjective and etale, with $T$ quasi-compact and
quasi-separated. There is a finite, finitely presented, surjective morphism
$r:T'\to T$ and a finite open covering $T'=\bigcup_aW_a$ such that every
$W_a\to T$ factors through $U\to T$.

## Proof

Choose finitely many affine opens $U_a\subset U$ whose images cover $T$ and
replace $U$ by their disjoint union. The resulting map is quasi-compact,
separated, etale, and has a finite upper bound $d$ on the cardinalities of
its geometric fibres. We induct on $d$. If $d=1$, the map is radicial and
etale, hence an open immersion; surjectivity makes it an isomorphism.

For $d>1$, apply the affine form of Zariski's Main Theorem to the separated
quasi-finite map $U\to T$: adjoining to $\mathcal O_T$ the integral elements
of the quasi-coherent algebra $u_*\mathcal O_U$ gives an integral
$\pi:\widetilde T\to T$ and a quasi-compact open immersion
$j:U\hookrightarrow\widetilde T$. Replace $\widetilde T$ by the
scheme-theoretic closure of $U$, so $U$ is schematically dense. The diagonal
section gives an open-and-closed decomposition

$$
U\times_T\widetilde T=U\amalg W.
$$

The image $V$ of $W\to\widetilde T$ is open and contains
$\widetilde T\setminus U$. Over a point of the dense open $U$, the fibre of
$W\to V$ is the fibre of $U\to T$ with the diagonal point removed, so it has
fewer than $d$ points. The number of points in a separated etale fibre
cannot increase under specialization: after writing the map locally as a
finite disjoint union of Jacobian etale algebra presentations, distinct idempotents at a
specialization lift to distinct idempotents at a generization. Thus every
geometric fibre of $W\to V$ has cardinality $<d$.

By induction there is an integral surjection $Z\to V$, locally factoring
through $W$. Apply the same integral-closure construction to
$Z\to\widetilde T$ and take the closure $Z'$ of $Z$; then
$Z'\times_{\widetilde T}V=Z$. If $C$ is the reduced closed complement
$\widetilde T\setminus V$, then $C\subset U$, and
$Z'\amalg C\to T$ is integral and surjective. Near a point of $Z$ it
factors through $W\to U$; near a point of $Z'\setminus Z$ it factors through
$C\subset U$. Hence it locally factors through the original cover.

Finally write this integral morphism as the inverse limit of its finite
finitely presented $T$-subalgebras. Choose finitely many affine opens on
which the factorization through $U$ is defined. Each open, each map to $U$,
the equalities over $T$, and surjectivity descend to a common finite stage:
the first three assertions are finite-presentation data, while failure of
surjectivity has quasi-compact open image and would persist after pullback to
the limit. That common stage is the required $T'$. This is the construction
located at Tag `09Z0`, with the degree induction and final finite stage
made explicit.

## Detailed form

Let $u:U\to T$ be a surjective etale morphism
[def-weil-pbc-scheme-conventions] and assume that $T$ is quasi-compact and
quasi-separated. There exist a finite set $J$, a finite, finitely presented,
surjective morphism

$$
 r:T'\longrightarrow T,
$$

a finite open covering $T'=\bigcup_{a\in J}W_a$, and $T$-morphisms
$\phi_a:W_a\to U$ such that

$$
 u\circ\phi_a=r|_{W_a}:W_a\longrightarrow T
 \qquad(a\in J).
$$

Equivalently, $r$ factors through $u$ Zariski locally on $T'$.

## Proof

This is the input of the finite refinement of surjective etale morphisms: for
a surjective etale morphism $u:U\to T$ with $T$ quasi-compact and
quasi-separated, there are a finite, finitely presented, surjective morphism
$r:T'\to T$, a finite open covering $T'=\bigcup_{a\in J}W_a$, and
$T$-morphisms $\phi_a:W_a\to U$ with $u\circ\phi_a=r|_{W_a}$ for every $a\in
J$, i.e. $r$ factors through $u$ Zariski locally on $T'$ (Stacks Project,
Lemma 37.45.7, Tag [09Z0](https://stacks.math.columbia.edu/tag/09Z0)). The
blueprint records this single assertion in the displayed form and proves
separately all of its consequences (the degree-zero comparisons over
henselian pairs); the proof, which refines the affine Zariski covering of $T$
and uses the local structure of etale morphisms, is not decomposed here.
