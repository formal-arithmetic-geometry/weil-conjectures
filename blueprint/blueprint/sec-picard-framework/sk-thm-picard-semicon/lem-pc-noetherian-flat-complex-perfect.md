+++
id = "lem-pc-noetherian-flat-complex-perfect"
kind = "lemma"
title = "A bounded flat complex with finite cohomology over a Noetherian ring"
order = 672
uses = ["def-pc-perfect-complex", "def-weil-abstract-derived-category"]
+++
Let $A$ be a Noetherian ring and let $C$ be an object of the
derived category
$D(A\text{-}\mathrm{Mod})$. Suppose that $C$ has a bounded
representative by flat $A$-modules and that every $H^i(C)$ is a
finite $A$-module. Then $C$ is represented by a bounded complex
of finite projective $A$-modules, hence is
perfect.

## Proof

Choose a flat representative $F^\bullet$ concentrated in degrees
$[a,b]$. In particular, for every $A$-module $N$, the complex
$F^\bullet\otimes_A N$ has no cohomology in degrees less than $a$.

We first construct a bounded-above complex $P^\bullet$ of finite
free modules, with $P^i=0$ for $i>b$, and a quasi-isomorphism
$P^\bullet\to F^\bullet$. Here are the steps of the construction.
Choose finitely many cycles representing generators of $H^b(F)$.
They give a map from a finite free module placed in degree $b$
to $F$. Its cone has zero cohomology in degrees at least $b$ and
finite cohomology in every degree: this follows from the long
exact sequence and the fact that kernels and cokernels of maps
between finite modules over a Noetherian ring are finite.
Suppose finite free terms in degrees $r,\ldots,b$ and a map from
that truncated complex to $F$ have been chosen so that its cone
has no cohomology in degrees at least $r$. Choose finitely many
cycles generating the cone's cohomology in degree $r-1$.
A cone cycle consists of a vector in the existing degree-$r$
term and a vector of $F^{r-1}$ satisfying the cone cycle
equations. Use these vectors to define the differential from a
new finite free degree-$(r-1)$ term and its map to $F^{r-1}$.
The cone equations give both $d^2=0$ and the chain-map identity.
The new cone has zero cohomology in degrees at least $r-1$,
and still has finite cohomology in every degree by the same
long exact sequence. Continuing downward gives $P$; in each
fixed degree the terms and maps stabilize, and the resulting
cone is acyclic. This proves the asserted quasi-isomorphism in
the derived category of [def-weil-abstract-derived-category].

A bounded-above complex of flat modules computes derived tensor
products. Indeed, its tensor product with an acyclic complex
is acyclic by applying the usual finite-complex argument to
successively longer bounded truncations and taking their
filtered colimit; tensor products and filtered colimits of
modules are exact in this calculation. Thus both $P$ and $F$
compute $C\otimes_A^{\mathbf L}N$.
Put $Q=\operatorname{coker}(P^{a-1}\to P^a)$. Since $P$ has no
cohomology below $a$, its left tail

$$
\cdots\longrightarrow P^{a-2}\longrightarrow P^{a-1}
\longrightarrow P^a\longrightarrow Q\longrightarrow0
$$

is a free resolution of $Q$. For every module $N$ it gives

$$
\operatorname{Tor}_1^A(Q,N)
=H^{a-1}(P^\bullet\otimes_A N)
=H^{a-1}(F^\bullet\otimes_A N)=0 .
$$

The Tor criterion for flatness makes $Q$ flat. It is finitely
presented, being the cokernel of a map between finite free
modules, so it is finite projective. Replacing the part of $P$
in degrees at most $a$ by $Q$ in degree $a$ gives a
quasi-isomorphic complex concentrated in $[a,b]$, all of whose
terms are finite projective, as required.
