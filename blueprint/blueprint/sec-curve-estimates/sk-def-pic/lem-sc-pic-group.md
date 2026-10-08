+++
id = "lem-sc-pic-group"
kind = "lemma"
title = "$\\operatorname{Pic}(C)$ is a group"
order = 886
uses = ["def-sc-curves", "def-sc-invertible-module", "lem-sc-invertible-dual"]
+++
Let $C$ be a curve. Tensor product makes
the set of isomorphism classes of
invertible modules an abelian
group: associative with unit $\mathcal O_C$, with inverse
$\mathcal L\mapsto\mathcal L^{\vee}$.

## Proof

Associativity, commutativity and the unit property of $\otimes$ are
the standard properties of tensor product of quasi-coherent modules.
By [lem-sc-invertible-dual],
$\mathcal L\otimes\mathcal L^{\vee}\cong\mathcal O_C$, so
$\mathcal L^{\vee}$ is an inverse.
