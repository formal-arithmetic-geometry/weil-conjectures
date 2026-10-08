+++
id = "thm-pc-criterion"
kind = "theorem"
title = "The representability criterion"
order = 835
uses = ["def-pc-cover", "def-pc-open-subfunctor", "def-pc-representable-functor", "def-pc-subfunctor", "def-pc-zariski-sheaf-property", "lem-pc-schemes-criterion"]
lean = ["AlgebraicGeometry.isRepresentable_of_representable_open_subfunctor"]
+++
(Picard Schemes of Curves, Lemma 44.5.1, Tag
[0B9Q](https://stacks.math.columbia.edu/tag/0B9Q).)
Let $k$ be a field and let
$G:(\mathit{Sch}/k)^{\mathrm{op}}\to\textit{Groups}$ be a functor. With the
terminology of
Definition [def-pc-subfunctor], assume:

1. **(1)** $G$ satisfies the sheaf property for the Zariski topology ([def-pc-zariski-sheaf-property]);
1. **(2)(a)** there exists a subfunctor $F\subseteq G$ such that $F$ is
representable;
1. **(2)(b)** $F\subseteq G$ is representable by open immersions ([def-pc-open-subfunctor]);
1. **(2)(c)** for every field extension $K$ of $k$ and every
$g\in G(K)$ there exists $g'\in G(k)$ such that $g'g\in F(K)$.

Then $G$ is representable by a group scheme over $k$.

## Proof

Apply [lem-pc-schemes-criterion] with $S=\operatorname{Spec}(k)$ and $I=G(k)$: for
$i=g'\in I$ let $F_i\subseteq G$ be the subfunctor

$$
F_i(T):=\{g\in G(T):g'g\in F(T)\}.
$$

Then $F_i\cong F$ via multiplication by $g'$ (a natural isomorphism
because $G$ is a functor with values in groups), so $F_i$ is
representable by (2)(a), and $F_i\subseteq G$ is representable by open
immersions: the map $F_i\to G$ is isomorphic (via multiplication by
$g'$) to the inclusion $F\to G$ of (2)(b), and the base change of a
natural isomorphism is a natural isomorphism. The family
$(F_i)_{i\in I}$ covers $G$ ([def-pc-cover]): given $g\in G(T)$, for each point $t\in T$
let $\kappa=\kappa(t)$ and let $j:\operatorname{Spec}\kappa\to T$; by (2)(c) applied to
$j^*g\in G(\kappa)$ there is $g'\in G(k)$ with
$g'j^*g\in F(\kappa)$, i.e. $j^*g\in F_{g'}(\kappa)$. By (2)(b) (the
open-immersion property for the pair $(T,\xi)$ with $\xi=g$, in the sense
of [def-pc-subfunctor]) there is an open
$U_\xi^{g'}\subseteq T$ such that a morphism $u:T'\to T$ factors through
$U_\xi^{g'}$ iff $u^*g\in F_{g'}(T')$; taking $T'=\operatorname{Spec}\kappa$ with
$j$ and noting that $j$ factors through the open $U$ iff the image point
$t$ lies in $U$, we find $t\in U_g^{g'}$ for the suitable $g'$, so the
open sets $U_g^{g'}$ ($g'\in G(k)$) cover $T$, and
$g|_{U_g^{g'}}\in F_{g'}(U_g^{g'})$ by the criterion. This verifies
(2)(c) of [lem-pc-schemes-criterion] (in the form of the covering
condition [def-pc-subfunctor]), while (2)(a), (2)(b) for the family
$(F_i)$ are what we just proved and (1) is the hypothesis; hence $G$ is
representable by a scheme. As $G$ takes values in groups and the
representing object is unique up to unique isomorphism, the group
structure on $G$ makes it a group scheme (the group-valued sheaf
structure is given; see the usual Yoneda argument, cf. [def-pc-representable-functor]).
