+++
id = "sk-d-monodromy"
kind = "section"
title = "Represented degree data and monodromy"
order = 2499
uses = ["sk-d-geometry", "sk-d-linear"]
lean = ["AlgebraicGeometry.Monodromy.DegreeDatum", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.arithmeticMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.geometricMonodromy", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.frobenius", "AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.IsSemisimple"]
+++
*Definition (sketch).*

A degree datum consists of a group $W$, a surjective homomorphism
$\deg:W\to\mathbf Z$, and a chosen element $\gamma$ of degree $1$.
Put $P=\ker(\deg)$; every $w$ has the form $u\gamma^{\deg w}$ with
$u\in P$. A represented datum adds a representation
$\rho:W\to\GL(V)$. Its arithmetic and geometric monodromy groups are
the reduced Zariski closures

$$
G=\overline{\rho(W)},\qquad H=\overline{\rho(P)},\qquad F=\rho(\gamma).
$$

These names concern the degree datum only; no topology or sheaf is
required in this subsection. A semisimple datum means that $V$ is a
semisimple $W$-representation.

Uses: [sk-d-geometry], [sk-d-linear]
