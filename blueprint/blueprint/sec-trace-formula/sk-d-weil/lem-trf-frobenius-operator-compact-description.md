+++
id = "lem-trf-frobenius-operator-compact-description"
kind = "lemma"
title = "Compact-support description of the global Frobenius"
order = 2298
uses = ["def-trf-coefficient-conventions", "def-trf-frobenius-operators", "def-trf-iterated-weil-map", "def-weil-derived-direct-image", "def-weil-finite-field-fiber", "def-weil-global-geometric-frobenius", "prop-trf-scheme-galois-comparison", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
Fix the global finite-field
datum and the coefficient
conventions, and let $(K,\varphi)\in D^b_{ctf,\mathrm W}(X,A)$. Then
the $m$-th iterate $F_{c,K}^{\,m}$ of the global geometric
Frobenius of [def-trf-frobenius-operators] is the composite

$$
F_{c,K}^{\,m}=R\Gamma_c(X,\varphi^{[m]})\circ g_{\gamma,c}^{m,*},
$$

where $\varphi^{[m]}$ is the iterated Weil isomorphism of
[def-trf-iterated-weil-map] and $g_{\gamma,c}^{m,*}$ is the
compact-support base-change isomorphism along the automorphism
$g_\gamma^m$ of the
global geometric
Frobenius action.

## Proof

By [def-trf-frobenius-operators] the operator $F_{c,K}^{\,m}$ is
the composite of the canonical direct-image identification of
[def-weil-derived-direct-image] with the compact-support global
geometric Frobenius action of
[def-weil-global-geometric-frobenius] applied to
$\varphi^{[m]}$ of [def-trf-iterated-weil-map]. That action
transports the pair $(g_\gamma^m,Lg_\gamma^{m*}\varphi^{[m]})$ along
the compact-support base-change identification for the finite
automorphism $g_\gamma^m$: on the coefficient complex the transport
is $R\Gamma_c(X,\varphi^{[m]})$ by
[def-trf-coefficient-conventions], and on the scheme variable it is
the base-change isomorphism $g_{\gamma,c}^{m,*}$. The comparison
between the scheme Frobenius and the geometric Frobenius that underlies
this transport is [prop-trf-scheme-galois-comparison], whose input
is the invariance of the site under the universal homeomorphism
$\Phi^m$ between them, [thm-weil-pbc-universal-homeomorphism-invariance];
no further choice enters. The composite is therefore the displayed
one.
