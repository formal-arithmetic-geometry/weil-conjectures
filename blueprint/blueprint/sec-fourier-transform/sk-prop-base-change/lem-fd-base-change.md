+++
id = "lem-fd-base-change"
kind = "lemma"
title = "Base change of the transform"
order = 2703
lean = ["AlgebraicGeometry.Etale.fourierTransformBaseChangeIso"]
uses = ["def-fd-kernel", "def-fd-transform", "def-weil-pbc-scheme-conventions", "lem-fd-as-lisse", "sbc-prop-extension-by-zero-and-arbitrary-base-change", "thm-weil-pbc-qbar"]
+++
Let $g:S'\to S$ be a morphism of separated finite-type schemes over $k_0$, and let $V'=V\times_SS'$. For $K\in D^b_c(V,E)$ there is a canonical identification

$$
\operatorname{FT}_\psi(g^*K)\cong g^*\operatorname{FT}_\psi(K).
$$

## Proof

The compactly supported pushforward $p_{2,!}$ of [def-fd-transform] is the composite of extension by zero along a chosen compactification $\bar p_2$ of $p_2$ with the direct image along the proper morphism $\bar p_2$; extension by zero commutes with arbitrary base change by [sbc-prop-extension-by-zero-and-arbitrary-base-change], and the direct image of a proper morphism satisfies the $\overline{\mathbf Q}_\ell$ proper base change of [thm-weil-pbc-qbar], so for the cartesian square of the base change the identification

$$
g^*p_{2,!}\cong p'_{2,!}\,g_V^*,\qquad g_V:V'\times_{S'}V'^\vee\to V\times_SV^\vee,
$$

holds. The integrand base changes by pullback: $g_V^*(p_1^*K\otimes^L\mathcal K_\psi)\cong{p_1'}^*(g^*K)\otimes^Lg_V^*\mathcal K_\psi$, and $g_V^*\mathcal K_\psi\cong\mathcal K'_\psi$ because the pairing $b'$ is the base change of $b$ and the lisse Artin–Schreier sheaf of [lem-fd-as-lisse] pulls back to the sheaf attached to the base-changed function ([def-fd-kernel]). Combining these identifications, and noting that the shift $[r]$ of [def-fd-transform] commutes with pullback, gives the displayed isomorphism.
