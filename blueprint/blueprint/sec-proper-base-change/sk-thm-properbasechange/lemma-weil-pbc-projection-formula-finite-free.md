+++
id = "lemma-weil-pbc-projection-formula-finite-free"
kind = "lemma"
title = "Finite-free projection formula"
order = 1265
uses = ["def-weil-pbc-projection-formula-arrows"]
+++
For $F=\Lambda^N[a]$, the maps $\pi_{h,E,F}$ and $\rho_{h,E,F}$ are inverse:

$$
\rho_{h,E,F}\pi_{h,E,F}=1,\qquad
\pi_{h,E,F}\rho_{h,E,F}=1.
$$

## Proof

Both source and target are the shift by $a$ of a finite direct sum of $N$
copies of $Rh_*E$. A right adjoint preserves finite products, and in an
additive category finite products are finite coproducts. Under these two
identifications, the counit defining $\pi$ is the identity in every summand.
The map $\rho$ is the reverse finite-sum identification, so the two displayed
composites are componentwise identities.
