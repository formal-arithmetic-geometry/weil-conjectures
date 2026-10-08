+++
id = "sk-i-topology"
kind = "section"
title = "Topological invariance"
order = 2357
uses = ["sec-six-functors", "sec-smooth-purity", "sk-d-setup", "sk-d-six", "sk-thm-sf-package"]
lean = ["AlgebraicGeometry.ProEtale.isEquivalence_leftDerivedUpperStar_of_isFinite"]
+++
*Proposition (sketch).*

For a finite universal homeomorphism $r:X\to Y$,
pullback is an equivalence
$r^*:D^b_{ctf}(Y,A)\simeq D^b_{ctf}(X,A)$, with inverse $Rr_*=Rr_!$ and
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
[sk-thm-sf-package]. A reduction is a finite universal homeomorphism, so the
reduction clause is a special case.

Uses: [sk-d-setup], [sk-d-six], [sk-thm-sf-package]
