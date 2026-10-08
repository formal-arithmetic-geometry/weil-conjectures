+++
id = "cor-fin-deligne-open-over-field"
kind = "theorem"
title = "Higher open direct images over a field"
order = 1638
tags = ["latex:corollary"]
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "def-weil-pbc-scheme-conventions", "thm-fin-deligne-generic-open"]
+++
Let $k$ be a field of characteristic different from $\ell$,
let $j:X\hookrightarrow Y$ be an open immersion of finite-type
$k$-schemes, and let $F$ be a constructible
$\mathbf F_\ell$-sheaf. Then $Rj_*F\in D^b_c(Y,\mathbf F_\ell)$.
The notation refers to ordinary derived categories.

## Proof

Apply [thm-fin-deligne-generic-open] with
$S=\operatorname{Spec}k$. Its only nonempty open is $S$
itself, so the generic conclusion is the assertion on all of $Y$.
No stratification of $Y$ and no closed-base-change assertion
for $Rj_*$ is needed here.
