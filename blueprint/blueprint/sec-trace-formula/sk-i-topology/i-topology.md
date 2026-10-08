+++
id = "i-topology"
kind = "theorem"
title = "Topological invariance"
order = 2358
uses = ["def-trf-coefficient-conventions", "prop-functor-package"]
tags = ["latex:proposition"]
+++
For a finite universal homeomorphism $r:X\to Y$,
pullback is an equivalence
$r^*:D^b_{ctf}(Y,A)\simeq D^b_{ctf}(X,A)$ (the categories of
[def-trf-coefficient-conventions]), with inverse $Rr_*=Rr_!$ and
invertible unit and counit. This includes reduction.

## Proof

Base change $V\mapsto V\times_YX$ is an equivalence of the small étale
categories, natural in the scheme and compatible with identities and
composites, and it preserves and reflects jointly surjective families,
because the underlying map of $r$ and of every base change of $r$ is a
homeomorphism. Its inverse functors are $r^{-1}$ and $r_*$, so the two
categories of étale sheaves are equivalent, with $r^{-1}$ exact and
$r_*$ its quasi-inverse. Exactness carries an injective resolution to an
injective resolution, which gives the compatibility with cohomology and
hence the statement on derived categories. Constructibility and finite
Tor amplitude are preserved on both sides, so the equivalence restricts to
$D^b_{ctf}$; $Rr_*=Rr_!$ because $r$ is finite, hence proper, by
[prop-functor-package]. A reduction is a finite universal homeomorphism, so the
reduction clause is a special case.

Uses: [def-trf-coefficient-conventions], [prop-functor-package]
