+++
id = "lem-sc-invertible-dual"
kind = "lemma"
title = "Duals of invertible modules"
order = 684
uses = ["def-sc-curves", "def-sc-invertible-module"]
+++
Let $C$ be a curve and $\mathcal L$ an
invertible module. Then
$\mathcal L^{\vee}$ is invertible, the evaluation map

$$
\operatorname{ev}:\mathcal L\otimes\mathcal L^{\vee}\to\mathcal O_C,
\qquad x\otimes f\mapsto f(x),
$$

is an isomorphism, and the canonical map
$\mathcal L\to(\mathcal L^{\vee})^{\vee}$ is an isomorphism.

## Proof

All assertions are local in the Zariski topology: on an open $U$
with $\mathcal L|_U\cong\mathcal O_U$, one has
$\mathcal L^{\vee}|_U\cong\mathcal O_U$, and the maps in question
become the standard isomorphisms $\mathcal O_U\otimes\mathcal O_U\to \mathcal O_U$, $f\otimes g\mapsto fg$, and
$\mathcal O_U\to\mathcal O_U$, $f\mapsto(g\mapsto fg)$.
