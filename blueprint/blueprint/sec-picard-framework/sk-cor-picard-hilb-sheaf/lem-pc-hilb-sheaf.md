+++
id = "lem-pc-hilb-sheaf"
kind = "lemma"
title = "$\\operatorname{Hilb}^d$ is an fppf sheaf"
order = 774
uses = ["def-pc-finite-locally-free", "def-pc-fppf-site", "def-pc-hilb-functor", "lem-pc-descent-finite-flat-closed-subschemes", "lem-pc-hilb-functorial"]
lean = ["AlgebraicGeometry.isSheaf_hilbertPresheaf"]
+++
(Picard Schemes of Curves, Lemma 44.2.1, Tag
[0B95](https://stacks.math.columbia.edu/tag/0B95), which asserts the
sheaf property for the fpqc topology; the fppf case asserted here is the
consequence of it used below.) Let $X\to S$ be
a morphism of schemes and $d\geq0$. The functor
$\operatorname{Hilb}^d_{X/S}$ satisfies the sheaf
property for the fppf topology.

## Proof

Let $\{T_i\to T\}_{i\in I}$ be an fppf covering of schemes over $S$
([def-pc-fppf-site]; an fppf covering is flat, locally of finite
presentation and surjective, hence faithfully flat: it is an fpqc
covering in particular) and let $Z_i\in\operatorname{Hilb}^d_{X/S}(T_i)$ be objects
such that $Z_i$ and $Z_{i'}$ map (under the restriction maps of [lem-pc-hilb-functorial]) to the same element of
$\operatorname{Hilb}^d_{X/S}(T_i\times_TT_{i'})$; say $Z_i$ corresponds to a closed
subscheme $\varphi_i:Z_i\hookrightarrow X_{T_i}$ (the definition
[def-pc-hilb-functor]) and the compatibility means: the two
pullbacks of $\varphi_i$ and $\varphi_{i'}$ to
$X_{T_i\times_TT_{i'}}$ are equal (in particular their composite
closed subschemes agree). By effective descent of finite flat closed subschemes
([lem-pc-descent-finite-flat-closed-subschemes], applied to the fpqc
covering $\{T_i\to T\}$; this uses exactly the given compatibility of the
$Z_i$'s over the double intersections) there is a closed subscheme
$Z\subseteq X_T$ with $Z\times_TT_i=Z_i$ for every $i$, and $Z\to T$ is
finite locally free of degree $d$ ([def-pc-finite-locally-free]): thus
$Z\in\operatorname{Hilb}^d_{X/S}(T)$ restricts to the $Z_i$. Such a $Z$ is unique by the uniqueness in
[lem-pc-descent-finite-flat-closed-subschemes]; hence $\operatorname{Hilb}^d$
satisfies the sheaf property for fppf coverings.
