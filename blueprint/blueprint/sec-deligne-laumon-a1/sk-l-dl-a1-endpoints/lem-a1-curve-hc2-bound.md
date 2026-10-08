+++
id = "lem-a1-curve-hc2-bound"
kind = "lemma"
title = "Top compact-support bound on a curve"
order = 2734
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "lem-a1-affine-hc2", "lem-a1-subquotient-extension-bounds", "lem-tw-tate-twist-weight-shift"]
+++
If $C_0$ is a smooth affine curve and $\mathcal F$ is lisse and
punctually $\iota$-pure of weight $w$, then
$H_c^2(C,\mathcal F)$ has weights at most $w+2$.

## Proof

The coinvariant description [lem-a1-affine-hc2] realizes the group
as a quotient of the local generic fiber $V=\mathcal F_{\bar\eta}$
followed by the twist $(-1)$. The quotient does not increase weights
by [lem-a1-subquotient-extension-bounds] (every eigenvalue of a
quotient is an eigenvalue of the pure module $V$ of weight $w$), and
the twist $(-1)$ in [lem-tw-tate-twist-weight-shift] raises
weights by two, giving weights at most $w+2$.
