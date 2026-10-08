+++
id = "cor-pur-vector-bundle-purity"
kind = "theorem"
title = "Vector-bundle purity"
order = 1990
tags = ["latex:corollary"]
uses = ["cor-amb-affine-space-adjunction", "def-amb-p1-trace", "def-amb-vector-integration", "def-coefficient-twists-detailed", "def-pur-conventions", "def-weil-derived-tensor", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-amb-affine-space-top-trace", "lem-amb-linear-trace-invariance", "thm-amb-vector-bundle-purity", "thm-sf-ambient-adjoint-class", "thm-weil-pbc-site-comparison"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $\pi:E\to B$ be a vector bundle of constant rank $r$ with zero
section $z$. For every $K\in D^b_{ctf}(B,\Lambda)$ there is a
canonical isomorphism

$$
R\pi^!K\;\xrightarrow{\ \sim\ }\;L\pi^*K(r)[2r],
$$

compatible with base change, with direct sums of vector bundles, and
with the adjunctions; in particular

$$
\omega_\pi=R\pi^!\Lambda_B\;\cong\;\Lambda_E(r)[2r],
$$

and the identification is compatible with the finite reduction of the
coefficients.

## Proof

At finite coefficient level on the ordinary etale site,
[thm-amb-vector-bundle-purity] constructs exactly the adjoint
of integration against the globally defined trace of
[def-amb-vector-integration]. It is an isomorphism for every
complex, hence in particular for the coefficients here.
The comparison of actual right adjoints in
[thm-sf-ambient-adjoint-class], together with
[thm-weil-pbc-site-comparison], transports this isomorphism and
its counit to the stated etale-origin category.

The compatibility claims concern these specified maps. On a
trivializing open the integration is the ordered affine-space counit
of [cor-amb-affine-space-adjunction]. The explicit projective-line
trace [def-amb-p1-trace] and its diagonal Kummer class commute
with coefficient reduction and base change, and composition of their
adjunctions gives the corresponding compatibilities for affine space.
For a direct sum of bundles choose simultaneous trivializations; the
two integrations are the same iterated counit, with the additive
twists of [def-coefficient-twists-detailed]. These equalities descend as
equalities between degree-zero sheaves on the base, because
[lem-amb-affine-space-top-trace] identifies every local source
with $\Lambda$, and [lem-amb-linear-trace-invariance] gives
agreement on overlaps. Transposing these equalities proves all the
claimed compatibilities. The proof precedes general smooth purity.
