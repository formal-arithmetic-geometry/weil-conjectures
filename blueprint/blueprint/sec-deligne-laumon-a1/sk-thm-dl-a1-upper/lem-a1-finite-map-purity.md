+++
id = "lem-a1-finite-map-purity"
kind = "lemma"
title = "Purity under finite etale pushforward"
order = 2797
uses = ["def-weil-pbc-scheme-conventions", "def-weil-punctual-weights", "lemma-weil-pbc-finite-stalk-formula"]
+++
If $g$ is finite etale and $\mathcal F$ is punctually $\iota$-pure
of weight $w$, then $g_*\mathcal F$ is punctually $\iota$-pure of
weight $w$.

## Proof

Fix a closed point $y$ of the target.
By [lemma-weil-pbc-finite-stalk-formula], the geometric stalk of
the direct image is the direct sum over all geometric points above
$\bar y$. A closed point $x$ above $y$, of residue degree
$e=[\kappa(x):\kappa(y)]$, contributes a Frobenius cycle of
$e$ copies of $\mathcal F_{\bar x}$.
The $e$-th power of $F_y$ on each copy is $F_x$.
Consequently every eigenvalue $\lambda$ of $F_y$ on this cycle
satisfies $\lambda^e=\alpha$ for an eigenvalue $\alpha$ of $F_x$.
Purity in [def-weil-punctual-weights] gives

$$
|\iota(\lambda)|^e=|\iota(\alpha)|
=q_x^{w/2}=q_y^{ew/2},
$$

so $|\iota(\lambda)|=q_y^{w/2}$.
All cycles have this property, proving purity of the pushforward.
