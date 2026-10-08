+++
id = "thm-cbc-finite-extension"
kind = "theorem"
title = "Compact-support base change over a finite extension"
order = 1644
uses = ["def-cbc-compact-support-square", "def-weil-pbc-rational-category", "lem-weil-compact-support-representative-independence", "prop-finite-compact-support-constructibility", "prop-weil-pbc-rational-transport", "thm-cbc-complete-proetale"]
+++
For every finite $E/\Ql$, every
compact-support
base-change square with $f$ separated of finite type and $g$
arbitrary, and every $K\in\Dbc(X,E)$ (in the sense of
[def-weil-pbc-rational-category]), whose reductions satisfy the
constructibility and amplitude conditions of
[prop-finite-compact-support-constructibility],

$$
Lg^*Rf_!K\xrightarrow{\ \sim\ }Rf'_!Lg'^*K
\quad\text{in }\Dbc(Y',E).
$$

This is independent of the integral lattice and natural and coherent
for identities and pasted squares.

## Proof

Choose an integral lattice for $K$. The isomorphism of
[thm-cbc-complete-proetale] is an isomorphism of
$\mathcal O_E$-linear functors on the integral constructible
categories, so by [prop-weil-pbc-rational-transport] it remains
an isomorphism after the rationalization of
[def-weil-pbc-rational-category]; the constructible landing is
the finite-level condition of the statement. Independence of the
lattice (both sides are lattice-independent by
[lem-weil-compact-support-representative-independence]) and
coherence are inherited from the integral level.
