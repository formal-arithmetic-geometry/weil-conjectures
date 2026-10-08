+++
id = "lem-sc-zariski-dimension-bound"
kind = "lemma"
title = "The Zariski dimension bound"
order = 1557
uses = ["def-sc-zariski-cohomology", "def-sc-zariski-flasque", "def-sc-zariski-site", "def-weil-pbc-scheme-conventions", "lem-sc-zariski-filtered-cohomology", "lem-sc-zariski-flasque-acyclic"]
+++
Let $X$ be a Noetherian
scheme of finite dimension $d$.
For every abelian sheaf $F$ on [def-sc-zariski-site],

$$
H^q(X_{\rm Zar},F)=0\quad(q>d),
$$

with cohomology as in [def-sc-zariski-cohomology].

## Proof

We induct on $d$. When $d=0$, the Noetherian scheme
has a finite discrete underlying space, so its section
functor is a finite product of exact stalk functors.
Let $d>0$, and let $\eta_1,\ldots,\eta_m$ be the
generic points of the finitely many irreducible components.
Write $u_i:\{\eta_i\}\to X$ for inclusion of the one-point
topological space. Put

$$
T(F)=\prod_{i=1}^m u_{i*}F_{\eta_i}.
$$

On an open $V$, this is the product of $F_{\eta_i}$
over the generic points belonging to $V$.
Restriction maps are projections, so this is flasque
in the sense of [def-sc-zariski-flasque].
The adjunction map $F\to T(F)$ is the identity at each
generic stalk. At $\eta_i$, the other factors have
zero stalk: remove the other irreducible components
in a neighborhood of $\eta_i$.

We first treat a sheaf $G$ whose generic stalks all vanish.
For a closed $Z$ avoiding the $\eta_i$, put
$G_Z=\ker(G\to j_*G|_{X\setminus Z})$.
Then $G=\varinjlim_ZG_Z$. Indeed a section on an open
$V$ has an open zero locus, so its support is closed in
$V$ and avoids every generic point in $V$.
The closure of this support in $X$ still avoids all
$\eta_i$. For $\eta_i\in V$, use the open neighborhood
where the section vanishes. If $\eta_i\notin V$, then
$V$ misses its whole irreducible component; remove the
other finitely many components near $\eta_i$.
This gives a suitable $Z$ for each section.
Finite unions make the closed sets $Z$ directed.
Every such $Z$ has dimension at most $d-1$:
a chain of irreducible closed subsets of $Z$ can be
extended by a component of $X$ strictly containing its
largest member.

Give $Z$ its reduced closed subscheme structure, which
has the same underlying Noetherian space and dimension.
For $i:Z\to X$, the sheaf $G_Z$ equals $i_*i^{-1}G_Z$
on stalks. Closed direct image on topological sheaves is
exact, as its stalk is the given stalk on $Z$ and zero
outside $Z$; it preserves injectives since inverse image
is exact. Consequently its cohomology on $X$ is the
cohomology on $Z$. Induction and
[lem-sc-zariski-filtered-cohomology] give
$H^q(X,G)=0$ for $q>d-1$.

Apply this result to the kernel $K$ and cokernel $C$
of $F\to T(F)$, and let $I$ be its image.
Since $T(F)$ is acyclic by
[lem-sc-zariski-flasque-acyclic], the sequence
$0\to I\to T(F)\to C\to0$ gives
$H^q(X,I)\simeq H^{q-1}(X,C)$ for $q\geq2$.
It is zero for $q>d$. The long exact sequence of
$0\to K\to F\to I\to0$ now gives the same vanishing for
$F$, proving the induction.
