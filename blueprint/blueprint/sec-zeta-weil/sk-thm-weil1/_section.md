+++
id = "sk-thm-weil1"
kind = "section"
title = "Weil conjectures I: rationality and Euler product"
order = 2927
lean = ["AlgebraicGeometry.Scheme.zetaSeries_rational", "AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod"]
uses = ["sk-def-zeta", "sk-prop-euler", "sk-thm-rationality"]
+++
*Theorem (sketch).*

$Z(X_0,T)\in1+T\Z[[T]]\cap\Q(T)$ and
$Z(X_0,T)=\prod_{x\in|X_0|}(1-T^{\deg(x)})^{-1}$.

## Proof

Combine the rationality of [sk-thm-rationality] with the closed-point
product and the integrality of [sk-prop-euler].

Uses: [sk-def-zeta], [sk-prop-euler], [sk-thm-rationality]
