+++
id = "cor-weil-pbc-geometric-fiber-qbar"
kind = "theorem"
title = "Qbar-l geometric-fiber formula"
order = 1360
uses = ["cor-weil-pbc-geometric-fiber-finite", "cor-weil-pbc-geometric-fiber-finite-extension", "thm-weil-pbc-qbar"]
tags = ["latex:corollary"]
+++
In the setup of the finite-level geometric-fiber corollary, let
$K\in\Dbc(X,\Qlb)$. The descended exchange morphism is an isomorphism
$$
 L\bar y^*Rf_*K\xrightarrow{\sim}
 Ra_{\bar y,*}Li_{\bar y}^*K
 \quad\text{in }\Dbc(\operatorname{Spec}\Omega,\Qlb).
$$
For a representative $(E,K_E)$, this is represented over a finite overfield
by the finite-extension formula of
[cor-weil-pbc-geometric-fiber-finite-extension] applied to $T_{M/E}K_E$.

## Proof

Specialize [thm-weil-pbc-qbar] to the geometric-point base change; the
representative statement is the displayed form in [thm-weil-pbc-qbar].
