+++
id = "lem-weil-pbc-curve-constructible-reduction"
kind = "lemma"
title = "Reduction to constructible prime torsion"
order = 1153
uses = ["def-weil-pbc-eight-curve-assertions", "def-weil-pbc-etale-sheaves", "lemma-weil-pbc-curve-filtered-cohomology", "lemma-weil-pbc-eight-curve-devissage", "thm-weil-pbc-universal-homeomorphism-invariance"]
+++
For a proper finite-type curve $C$ and a torsion sheaf $F$, assertion
$\mathcal C_7(C,F)$ of [def-weil-pbc-eight-curve-assertions] follows
from its instances for reduced curves with constructible $\mathbf
F_r$-coefficients, for every prime $r$. The intervening coefficient passage is
governed by constructible subsheaves, finite primary decomposition, and the
exact sequence

$$
 0\to F[r]\to F\to F/F[r]\to0.
$$

## Proof

Let $C$ be a proper finite-type curve and $F$ a torsion sheaf. The reduction
$C_{\mathrm{red}}\hookrightarrow C$ is a universal homeomorphism, so by
invariance of the etale site under universal homeomorphisms we may replace $C$
by its reduction. The sheaf $F$ is the filtered colimit of its constructible
torsion subsheaves (the constructible approximation on a quasi-compact
quasi-separated scheme), so [lemma-weil-pbc-curve-filtered-cohomology] and the
naturality of the maps $\rho^q_{k'/k}$ reduce $\mathcal C_7(C,F)$ to its
instances for constructible $F$; the finite primary decomposition and the
exact sequence $0\to F[r]\to F\to F/F[r]\to0$ (iterated over the prime factors
of the torsion orders) reduce constructible $F$ by
[lemma-weil-pbc-eight-curve-devissage] to the instances with $\mathbf
F_r$-coefficients.
