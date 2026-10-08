+++
id = "sk-thm-sf-pf-field"
kind = "section"
title = "Projection formula: rational and algebraically closed stages"
order = 2097
uses = ["sk-thm-sf-pf-adic"]
lean = ["AlgebraicGeometry.Etale.hasProjectionFormula_field"]
+++
*Theorem (sketch).*

Let $K,L$ be obtained by rationalization from $\mathcal O_E$-objects, or
represented at a finite stage $E'/\Ql$. Then
$\operatorname{PF}_{f,K,L}$ is an isomorphism over $E$ and over $\Qlb$,
compatible with the extension functors and with finite reduction.

## Proof

Rationalization $-\otimes^L_{\mathcal O_E}E$ is exact, commutes with $Rf_!$,
$\otimes^L$ and $Lf^*$, and carries the mate-theoretic projection
transformation to the mate-theoretic projection transformation, since units
and counits are transported; an exact functor carries isomorphisms to
isomorphisms. For $\Qlb$ each object is represented over a finite stage by
def:weil-algebraically-closed-coefficients, and compatibility with scalar
extension makes the finite-stage system descend to the $2$-colimit.

Uses: `\Cref{thm-sf-pf-adic}`, `def-weil-algebraically-closed-coefficients`, `def-weil-rationalization-karoubi`
