+++
id = "lem-fet-galois-category"
kind = "theorem"
title = "$F_{\\bar y}$ is a Galois category"
order = 975
uses = ["def-galois-categories", "def-galois-category", "def-galois-fibre-functor", "def-weil-pbc-scheme-conventions", "lem-fet-finite-limits", "lem-galois-axioms", "lem-galois-geometric-fibre"]
+++
Let $Y$ be connected with a geometric point $\bar y\to Y$. Then
$\mathrm{F\acute Et}(Y)$ together with $F_{\bar y}$ is a Galois category.

## Proof

We verify the axioms of [def-galois-category] for the pair
$(\mathrm{F\acute Et}(Y),F_{\bar y})$ of [def-galois-categories]
and [def-galois-fibre-functor]; the scheme-theoretic notions used
are those of [def-weil-pbc-scheme-conventions].
Axioms (1), (3) and exactness in (4) follow from
[lem-fet-finite-limits]: a scheme etale over the spectrum of an
algebraically closed field is a disjoint union of copies of it, so base
change to $\bar y$ is the functor $P\mapsto|P_{\bar y}|$, which is exact
and takes finite values ([lem-galois-geometric-fibre]); the final statement of axiom (2) and the
reflection of isomorphisms remain.
Step 1: connected objects. If $Y'\to Y$ is a monomorphism in
$\mathrm{F\acute Et}(Y)$, then $Y'\to Y'\times_YY'$ is an isomorphism,
so $Y'\to Y$ is a monomorphism of schemes; an etale monomorphism is an
open immersion, being the composite of the graph
$Y'\to Y'\times_YY'$ with the open diagonal of the etale morphism
$Y'\to Y$. Since $Y'$ is finite over $Y$ and $Y$ is separated over
itself, $Y'\to Y$ is finite, hence closed; an open and closed immersion
is the inclusion of an open and closed subscheme. Hence $Y'$ is a
connected object of $\mathrm{F\acute Et}(Y)$ exactly when $Y'$ is
connected as a scheme, and every finite etale $Y'$ is a finite coproduct
of its connected components, which are the connected objects in the
categorical sense.
Step 2: $F_{\bar y}$ reflects isomorphisms. Let $f:Y'\to Y''$ induce a
bijection $|Y'_{\bar y}|\to|Y''_{\bar y}|$. Decomposing $Y''$ into
connected components and using Step 1, we may assume $Y''$ connected. A
finite etale morphism is finite locally free, so it is enough to show that
$f$ is finite locally free of degree $1$. This holds in a
neighbourhood of every point of $Y''$ lying over $\bar y$, and the
degree of a finite locally free morphism is locally constant in the target;
since $Y''$ is connected the degree is $1$ everywhere, so $f$ is an
isomorphism.
