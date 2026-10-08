+++
id = "sk-prop-av-divisible"
kind = "section"
title = "Surjectivity of multiplication by $n$ on points"
lean = ["AlgebraicGeometry.surjective_npow_points"]
order = 569
uses = ["sk-def-av", "sk-def-av-mult-n", "sk-prop-av-isogeny"]
+++
*Proposition (sketch).*

Let $A$ be an abelian variety over an algebraically closed field $k$
and $n\ge1$. Then $[n]:A(k)\to A(k)$ is surjective: $A(k)$ is a
divisible abelian group.

## Proof

By [sk-prop-av-isogeny], $[n]$ is finite flat and surjective; a finite
flat surjective morphism over the algebraically closed field $k$ is
surjective on $k$-points, because the fibre over $y\in A(k)$ is a
nonempty finite $k$-scheme, hence has a $k$-point.

Uses: [sk-def-av-mult-n], [sk-def-av], [sk-prop-av-isogeny]
