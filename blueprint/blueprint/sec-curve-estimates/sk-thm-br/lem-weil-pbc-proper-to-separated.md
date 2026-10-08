+++
id = "lem-weil-pbc-proper-to-separated"
kind = "lemma"
title = "Proper to a separated target"
order = 909
uses = ["def-weil-pbc-scheme-conventions", "lem-weil-pbc-closed-immersion-products", "lem-weil-pbc-closed-immersion-proper", "lem-weil-pbc-proper-base-change", "lem-weil-pbc-proper-composition"]
+++
Let $f:X\to Y$ be proper and let $g:X\to W$ be a $Y$-morphism with $W$
separated [def-weil-pbc-scheme-conventions] over $Y$. Then $g$ is proper.

## Proof

Write $g=\mathrm{pr}_W\circ\Gamma_g$ with $\Gamma_g=(1,g):X\to X\times_YW$
the graph. Since $W$ is separated over $Y$, its diagonal is a closed
immersion, and the graph is a base change of this diagonal along
$X\times_YW\to W\times_YW$, hence again a closed immersion (a base change is
a product of the type handled by
[lem-weil-pbc-closed-immersion-products], in the sense of
[def-weil-pbc-scheme-conventions]); it is proper by
[lem-weil-pbc-closed-immersion-proper]. The projection $X\times_YW\to W$ is a
base change of the proper $f$, hence proper by
[lem-weil-pbc-proper-base-change], and the composite $g$ is therefore proper
by [lem-weil-pbc-proper-composition].
