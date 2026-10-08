+++
id = "sk-def-ft"
kind = "section"
title = "The Fourier–Deligne transform"
order = 2692
lean = ["AlgebraicGeometry.Etale.fourierTransform"]
uses = ["sk-def-kernel", "sk-lem-as-properties"]
+++
*Definition (sketch).*

With $V_0\to S_0$ of rank $r$ as above and the projections
$p_1:V\times_SV^\vee\to V$, $p_2:V\times_SV^\vee\to V^\vee$, the
*Fourier–Deligne transform* of $K\in\Dbc(V,E)$ is

$$
\FT_\psi(K):=p_{2,!}\bigl(p_1^*K\otimes^L_E\mathcal K_\psi\bigr)[r].
$$

The shift $[r]$ — the relative dimension of $V_0/S_0$ — is part of the
definition: this is Laumon's normalization, the one for which inversion holds
without a further shift, up to the twist $(-r)$. The transform with the
inverse character is $\FT_{\psi^{-1}}$, whose kernel is
$\mathcal K_{\psi^{-1}}\cong\mathcal K_\psi^{-1}$ by P1. On $\Aone$ one has
$r=1$ and $\FT_\psi(K)=p_{2,!}(p_1^*K\otimes^L\mathcal K_\psi)[1]$; the
transform of the inverse character is the same construction with
$\psi^{-1}$ in the kernel. (Blueprint def:fd-transform.)

Uses: [sk-def-kernel], [sk-lem-as-properties]
