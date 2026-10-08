+++
id = "sk-prop-base-change"
kind = "section"
title = "P5: base change"
order = 2702
lean = ["AlgebraicGeometry.Etale.fourierTransformBaseChangeIso"]
uses = ["sk-def-ft"]
+++
*Proposition (sketch).*

For a morphism $g:S'\to S$ of separated finite-type $k_0$-schemes and
$V'=V\times_SS'$, there is a canonical identification
$\FT_\psi(g^*K)\cong g^*\FT_\psi(K)$ for $K\in\Dbc(V,E)$.
(Blueprint lem:fd-base-change.)

## Proof

Write $p_{2,!}$ as extension by zero along a compactification of $p_2$
composed with the direct image along the proper $\bar p_2$. Extension by zero
commutes with arbitrary base change
(sbc-prop-extension-by-zero-and-arbitrary-base-change) and proper direct
images satisfy $\Qlb$-coefficient proper base change
(thm:weil-pbc-qbar); hence $g^*p_{2,!}\cong p'_{2,!}g_V^*$ on the
base-changed square. The integrand base changes by pullback, and
$g_V^*\mathcal K_\psi\cong\mathcal K'_\psi$ because the pairing base changes
and the lisse Artin–Schreier sheaf pulls back to the sheaf of the
base-changed function ([sk-def-kernel]); the shift commutes with pullback.

Uses: [sk-def-ft]
