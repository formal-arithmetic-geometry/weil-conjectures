+++
id = "sk-d-weil-push"
kind = "section"
title = "Weil $!$-pushforward"
order = 2363
uses = ["sk-d-operator", "sk-d-relative-frob", "sk-d-six", "sk-d-weil", "sk-i-relative-frob", "sk-i-topology"]
lean = ["AlgebraicGeometry.ProEtale.WeilComplex.lowerShriekPush"]
+++
*Definition (sketch).*

For a Weil complex $(K,\varphi)$ on $X$, put $L=Rf_!K$.
Cartesian $!$-base change for
$X'_m$, together with
topological invariance for
$r_m$, gives the comparison

$$
\theta_{f,m}:\Phi_{Y,m}^*Rf_!K
\simeq Rf'_{m!}p_m^*K
\xrightarrow{\eta_{r_m}^*}Rf'_{m!}Rr_{m!}r_m^*p_m^*K
\simeq Rf_!\Phi_{X,m}^*K.
$$

The middle unit is invertible. Define
$\psi=Rf_!\varphi\circ\theta_{f,1}$; its iterates are
$\psi_m=Rf_!\varphi_m\circ\theta_{f,m}$ by base-change composition.
The same definition and identity apply to arbitrary Frobenius
coefficient morphisms of [sk-d-weil].

Uses: [sk-d-relative-frob], [sk-d-six], [sk-d-weil], [sk-i-relative-frob], [sk-i-topology]
