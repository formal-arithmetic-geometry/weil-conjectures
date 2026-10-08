+++
id = "sk-d-dl-general-weights"
kind = "section"
title = "Mixed upper bounds"
order = 2810
lean = ["AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost", "AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost"]
uses = ["sk-d-dl-a1-setup"]
+++
*Definition (sketch).*

Retain $k_0=\mathbf F_q$, geometric Frobenius, and
$\iota:\DLRQ\simeq\mathbf C$. A constructible Weil sheaf is
*$\iota$-mixed of weights at most $w$* if it has a finite filtration
with punctually pure quotients of weights at most $w$.
A bounded constructible Weil complex $K$ has weights at most $w$ if
$\mathcal H^bK$ is mixed of weights at most $w+b$ for every $b$.
Subobjects, quotients and extensions preserve these bounds: intersect a
filtration, take its images, or splice filtrations, respectively.
We work with separated finite-type $k_0$-schemes and the coefficient
framework of Section [sec-six-functors].

Uses: [sk-d-dl-a1-setup]
