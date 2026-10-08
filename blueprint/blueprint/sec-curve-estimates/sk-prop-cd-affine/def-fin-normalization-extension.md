+++
id = "def-fin-normalization-extension"
kind = "definition"
title = "Normalization in a finite extension"
order = 1014
uses = ["def-sc-normalization", "def-weil-pbc-scheme-conventions"]
+++
Let $X$ be an
integral scheme
with function field $K$, and let $L/K$ be finite.
The normalization of $X$ in $L$ is the relative
spectrum of the integral closure of $\mathcal O_X$ in
$L$, with its canonical map to $X$. On an
affine open
$\operatorname{Spec}B$, this is
$\operatorname{Spec}\overline B^{,L}$.
Integral closure commutes with localization, so these
affine constructions glue. For $L=K$, this is exactly
[def-sc-normalization]; finiteness is not included in
the definition.
