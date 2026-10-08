+++
id = "thm-pur-rational-and-qbar-purity"
kind = "theorem"
title = "Rational and $\\Qlb$ purity"
order = 2026
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-pbc-qbar-category", "def-weil-pbc-rational-category", "def-weil-scheme-morphism-properties", "prop-pur-rational-purity-transitivity-summands", "prop-weil-pbc-rational-transport", "thm-pur-adic-reconstruction"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$f:X\to Y$ be smooth separated of relative dimension $d$ over a
separated finite-type $k$-scheme, and let $K$ lie in the $E$-coefficient
category of [def-weil-pbc-rational-category], respectively the
$\Qlb$-coefficient category of [def-weil-pbc-qbar-category], presented
by a normalized integral system (a lattice) as in
[def-weil-pbc-rational-category]. Then

$$
\gamma_{f,K}:Lf^*K(d)[2d]\xrightarrow{\ \sim\ }Rf^!K
$$

is an isomorphism in the corresponding category: rationalization along
[prop-weil-pbc-rational-transport] and finite extension of coefficient
fields carry the adic purity isomorphism of
[thm-pur-adic-reconstruction] to the $E$- and $\Qlb$-purity
isomorphisms.

## Proof

Step 1: the $E$-stage. An $E$-object $K$ of
[def-weil-pbc-rational-category] is presented by a lattice
$K_{\mathcal O_E}\in D^b_{ctf}(\cdot,\mathcal O_E)$ with
$K_E=K_{\mathcal O_E}\otimes^L_{\mathcal O_E}E$. The adic purity
isomorphism

$$
\gamma_{f,K_{\mathcal O_E}}:\ Lf^*K_{\mathcal O_E}(d)[2d]
\xrightarrow{\ \sim\ }Rf^!K_{\mathcal O_E}
$$

of [thm-pur-adic-reconstruction] for the lattice, extended along
the exact functor $-\otimes^L_{\mathcal O_E}E$ (exact because
$\mathcal O_E\to E$ is flat), is an isomorphism

$$
\gamma_{f,K_E}:\ Lf^*K_E(d)[2d]\xrightarrow{\ \sim\ }Rf^!K_E
$$

between the $E$-objects, i.e. the $E$-purity isomorphism of
[def-weil-pbc-rational-category]. Step 2: the $\Qlb$-stage.
A $\Qlb$-object of [def-weil-pbc-qbar-category] is represented
by an $E$-object $K_E$ for some finite $E/\Ql$ (no idempotent is
needed, the finite-stage categories being idempotent complete); the
$\Qlb$-purity isomorphism is the transport of the $E$-purity
isomorphism of Step 1 along the scalar extension
$E\hookrightarrow\Qlb$, well defined by the independence of
[prop-pur-rational-purity-transitivity-summands].
