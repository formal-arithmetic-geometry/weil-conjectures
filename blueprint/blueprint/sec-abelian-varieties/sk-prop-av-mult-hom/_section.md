+++
id = "sk-prop-av-mult-hom"
kind = "section"
title = "The $n$-fold sum is a homomorphism"
lean = ["AlgebraicGeometry.isMonHom_npow_id"]
order = 493
uses = ["sk-cor-av-commutative", "sk-def-av-group-scheme", "sk-def-av-mult-n"]
+++
*Proposition (sketch).*

Let $G$ be a commutative group scheme over $k$ and $n\ge1$. Then the
$n$-fold sum map $[n]:G\to G$ is a homomorphism of group schemes.

## Proof

The sum map $m:G\times_kG\to G$ is a homomorphism when $G$ is
commutative (the group law of $G\times_kG$ is componentwise), so its
$n$-fold iterate $[n]$ is a composite of homomorphisms.

Uses: [sk-cor-av-commutative], [sk-def-av-group-scheme], [sk-def-av-mult-n]
