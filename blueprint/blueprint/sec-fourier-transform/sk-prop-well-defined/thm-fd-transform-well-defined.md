+++
id = "thm-fd-transform-well-defined"
kind = "theorem"
title = "Well-definedness of the Fourier–Deligne transform"
order = 2697
lean = ["AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible", "AlgebraicGeometry.Etale.fourierTransformBoundedConstructible"]
uses = ["def-fd-kernel", "def-fd-transform", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions", "prop-functor-package", "prop-kernel-lisse"]
+++
Let $S_0$ be a separated
scheme of finite type over $k_0$, let $V_0\to S_0$ be a vector
bundle of rank $r$ with dual $V_0^\vee$, let $E/\Ql$ be a finite
extension, and let $p_1,p_2$ be the projections of
[def-fd-transform]. Then for every $K\in D^b_c(V,E)$,

$$
\operatorname{FT}_\psi(K)\in D^b_c(V^\vee,E),
$$

and $\operatorname{FT}_\psi$ is an exact triangulated functor

$$
\operatorname{FT}_\psi:
D^b_c(V,E)\longrightarrow D^b_c(V^\vee,E).
$$

## Proof

The kernel $\mathcal K_\psi$ of [def-fd-kernel] is a lisse
rank-one module, hence of finite Tor amplitude [prop-kernel-lisse] in the
coefficient conventions of the proper-base-change chapter ([def-weil-pbc-qbar-category]). By [prop-functor-package] of the framework chapter, the derived
pullback $Lp_1^*$, the derived tensor product, and the derived
compact-support direct image $p_{2,!}$ (the compact-support direct
image of the separated finite-type $p_2$)
are exact triangulated functors on their constructible and finite-Tor
domains; hence $Lp_1^*K\otimes^L_E\mathcal K_\psi$ lies in
$D^b_c(V\times_SV^\vee,E)$, and its image under $p_{2,!}$
lies in $D^b_c(V^\vee,E)$; the shift $[r]$ of
[def-fd-transform] preserves boundedness and constructibility.
