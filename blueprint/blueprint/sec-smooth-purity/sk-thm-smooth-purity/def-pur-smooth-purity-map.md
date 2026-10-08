+++
id = "def-pur-smooth-purity-map"
kind = "definition"
title = "Smooth purity map"
order = 2012
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "thm-pur-cohomological-smoothness"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, let $f:X\to Y$ be smooth,
separated, of pure
relative dimension $d$, and let $K\in D^b_{ctf}(Y,\Lambda)$. The
*smooth purity map* is the composite

$$
\gamma_{f,K}:\;
Lf^*K(d)[2d]
\xrightarrow{\ \sim\ }
Lf^*K\otimes^L_{\Lambda_X}\Lambda_X(d)[2d]
\xrightarrow{\ \sim\ }
Lf^*K\otimes^L_{\Lambda_X}\omega_f
\xrightarrow{\ \sim\ }
Rf^!K,
$$

the first isomorphism being the canonical twist reassociation of
[def-coefficient-twists-detailed], and the
third the tensor formula of [thm-pur-cohomological-smoothness].
