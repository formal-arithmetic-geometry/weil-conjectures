+++
id = "thm-weil-pbc-finite-extension"
kind = "theorem"
title = "Proper base change over a finite extension"
order = 1357
uses = ["cor-weil-pbc-constructible-complete", "def-weil-pbc-cartesian-square", "def-weil-pbc-scheme-conventions", "prop-weil-pbc-rational-transport"]
+++
For every finite $E/\Ql$, every cartesian square
[def-weil-pbc-cartesian-square] with $f$ proper, and every
$K\in\Dbc(X,E)$,
$$
 Lg^*Rf_*K\xrightarrow{\sim}Rf'_*Lg'^*K
 \quad\text{in }\Dbc(Y',E).
$$

## Proof

Choose an integral lattice for $K$: the isomorphism of
[cor-weil-pbc-constructible-complete] is an isomorphism of
$\mathcal O_E$-linear functors on the integral constructible categories, so
by [prop-weil-pbc-rational-transport] it remains an isomorphism after
rationalization. The independence and coherence assertions are inherited
from the integral level.
