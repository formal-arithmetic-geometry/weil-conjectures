+++
id = "lem-kun-tensor-unit"
kind = "lemma"
title = "Tensor unit"
order = 1711
uses = ["def-kun-constant-sheaf", "def-weil-pbc-etale-sheaves"]
+++
For a commutative ring $\Lambda$ and
$E\in D(T_{\Et},\Lambda)$, both canonical unit constraints
$E\kunotimes{\Lambda}\underline{\Lambda}\to E$ and
$\underline{\Lambda}\kunotimes{\Lambda}E\to E$ are isomorphisms.

## Proof

The constant sheaf $\underline{\Lambda}$ is a flat
$\Lambda$-module sheaf, so the (underived) tensor product computes the
derived one; $E\otimes_\Lambda\underline{\Lambda}=E$ by the unit
constraint of the sheaf category, which is the assertion.
