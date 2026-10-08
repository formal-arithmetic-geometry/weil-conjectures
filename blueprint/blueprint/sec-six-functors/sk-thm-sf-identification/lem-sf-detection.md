+++
id = "lem-sf-detection"
kind = "lemma"
title = "Detection of isomorphisms at the point"
order = 2183
uses = ["lem-sf-point"]
+++
In the setting of [lem-sf-point], let $u:P\to Q$ be a morphism of the
point category. Then $u$ is an isomorphism if and only if
$\operatorname{Hom}_s(\Lambda[-r],u)$ is an isomorphism for every
$r\in\mathbf Z$.

## Proof

By [lem-sf-point] the functor $\Fib_s$ is an exact equivalence, so it
suffices to decide the question for bounded complexes of $A_{E,n}$-modules
with finite cohomology. There a morphism is an isomorphism in the derived
category if and only if it is a quasi-isomorphism, i.e. if and only if it
induces isomorphisms on all cohomology modules; and
$H^r(-)=\operatorname{Hom}_s(\Lambda[-r],-)$ by [lem-sf-point].
Equivalently, the cone of $u$ has vanishing cohomology, and a bounded
complex with vanishing cohomology is zero.
