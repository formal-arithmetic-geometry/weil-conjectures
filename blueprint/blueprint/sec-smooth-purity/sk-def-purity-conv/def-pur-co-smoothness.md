+++
id = "def-pur-co-smoothness"
kind = "definition"
title = "Cohomological smoothness"
order = 1896
uses = ["def-exchange-projection", "def-pur-conventions", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
a separated finite-type
morphism $f:X\to Y$ is *cohomologically smooth* if:

1. $\omega_f=Rf^!\Lambda_Y$ is tensor-invertible;
1. for every $K\in D^b_{ctf}(Y,\Lambda)$ the canonical map
(the mate of the projection formula of
[def-exchange-projection] with the adjunction counit)
$$
\theta_{f,K}:Lf^*K\otimes^L_{\Lambda_X}\omega_f
\longrightarrow Rf^!K
$$
is an isomorphism;
1. for every Cartesian square
$$
\begin{array}{ccc}
X'&\xrightarrow{\ g'\ }&X\\
f'\downarrow&&\downarrow f\\
Y'&\xrightarrow{\ g\ }&Y,
\end{array}
$$
the canonical base-change map
$Lg'^*\omega_f\to\omega_{f'}$ is an isomorphism.

At this stage no isomorphism $\omega_f\simeq\Lambda_X(d)[2d]$ is part
of the definition.
