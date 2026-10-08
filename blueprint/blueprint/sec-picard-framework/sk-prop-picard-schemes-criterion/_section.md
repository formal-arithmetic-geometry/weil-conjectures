+++
id = "sk-prop-picard-schemes-criterion"
kind = "section"
title = "The general representability criterion"
order = 775
uses = ["sk-def-av-jacobian"]
lean = ["AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable"]
+++
*Proposition (sketch).*

Let $G:(\Sch/S)^{\mathrm{op}}\to\mathsf{Set}$ be a Zariski sheaf and
$(F_i)_{i\in I}$ representable subfunctors, each representable by
open immersions, with $G=\bigcup_iF_i$ in the sense that for every
$T$ and $\xi\in G(T)$ there is an open covering $T=\bigcup_aT_a$ and
indices $i_a$ with $\xi|_{T_a}\in F_{i_a}(T_a)$. Then $G$ is
representable.

## Proof

*Step 1 (charts and transition maps).* Let $X_i$ represent $F_i$,
with universal element $\xi_i\in F_i(X_i)\subseteq G(X_i)$, and let
$U_{ij}\subseteq X_i$ be the open subscheme provided by the
representability of $F_j\subseteq G$ by open immersions: a morphism
$T\to X_i$ factors through $U_{ij}$ precisely when the pullback of
$\xi_i$ lies in $F_j(T)$. In particular
$\xi_i|_{U_{ij}}\in F_j(U_{ij})$, so it is induced by a unique
$\varphi_{ij}:U_{ij}\to X_j$ with
$\varphi_{ij}^*\xi_j=\xi_i|_{U_{ij}}$, and the same universal property
for $F_i\subseteq G$ makes $\varphi_{ij}$ factor through $U_{ji}$.

*Step 2 (the charts glue).* The composite
$\varphi_{ji}\circ\varphi_{ij}$ pulls $\xi_i$ back to $\xi_i|_{U_{ij}}$,
hence is the identity by the uniqueness of the representing morphism;
symmetrically for the other composite, so
$\varphi_{ij}:U_{ij}\to U_{ji}$ are mutually inverse isomorphisms. The
glueing compatibility
$\varphi_{ij}^{-1}(U_{ji}\cap U_{jk})=U_{ij}\cap U_{ik}$ holds because
both sides are the largest open $W\subseteq U_{ij}$ with
$\xi_i|_W\in F_k(W)$, and the cocycle condition holds because both
composites pull $\xi_k$ back to $\xi_i$ and that morphism is unique.
The glueing lemma for schemes then gives a scheme $X$ over $S$ with open
immersions $X_i\hookrightarrow X$ intersecting in the $U_{ij}$.

*Step 3 ($X$ represents $G$).* The $\xi_i$ agree on the overlaps,
so the Zariski sheaf property of $G$ produces a unique $\xi\in G(X)$
with $\xi|_{X_i}=\xi_i$, i.e. a natural transformation $h_X\to G$,
$a\mapsto a^*\xi$. It is injective: for $a,b:T\to X$ with
$a^*\xi=b^*\xi$ the open $a^{-1}(X_i)$ is the largest open over which
the pullback of $\xi$ lies in $F_i$, hence depends only on $a^*\xi$;
over it both $a$ and $b$ factor through $X_i$ and agree because $\xi_i$
is universal, and $h_X$ is a Zariski sheaf. It is surjective: for
$t\in G(T)$ the largest opens $T_i\subseteq T$ with
$t|_{T_i}\in F_i(T_i)$ cover $T$ by the covering hypothesis, each
$t|_{T_i}$ comes from a unique $a_i:T_i\to X_i$, these agree on overlaps
by the same uniqueness, and glue to the required $a:T\to X$ with
$a^*\xi=t$.

This is Stacks, Schemes, Lemma 26.15.4
([`01JJ`](https://stacks.math.columbia.edu/tag/01JJ)), the glueing input being Schemes,
Lemma 26.14.2; the detailed form is Blueprint 50,
`lem-pc-schemes-criterion`.
