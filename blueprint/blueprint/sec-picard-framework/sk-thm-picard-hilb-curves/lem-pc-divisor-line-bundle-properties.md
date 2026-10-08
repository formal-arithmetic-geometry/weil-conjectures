+++
id = "lem-pc-divisor-line-bundle-properties"
kind = "lemma"
title = "Properties of $\\mathcal{O}_X(D)$"
order = 792
uses = ["def-pc-base-change", "def-sc-effective-cartier-divisor", "def-sc-invertible-module", "lem-pc-closed-imm-base-change", "lem-pc-tensor-dual-invertible"]
+++
Let $S$ be a scheme and $D\subset S$ an
effective Cartier divisor.

1. $\mathcal{O}_S(D)$ is an
invertible $\mathcal{O}_S$-module.
1. If $g:Y\to S$ is a flat morphism and $D_Y=D\times_SY$, then
$\mathcal{I}_{D_Y}=g^*\mathcal{I}_D$ and $\mathcal{O}_Y(D_Y)\cong g^*\mathcal{O}_S(D)$.

## Proof

(1) By definition of an effective Cartier divisor, $\mathcal{I}_D$ is an
invertible $\mathcal{O}_S$-module; by [lem-pc-tensor-dual-invertible] its
dual $\mathcal{O}_S(D)=\mathcal{I}_D^\vee$ is invertible.

(2) The ideal sheaf of the base change is the pullback of the ideal
sheaf ([lem-pc-closed-imm-base-change]:
$\mathcal{I}_{D_Y}=\operatorname{im}(g^*\mathcal{I}_D\to\mathcal{O}_Y)=g^*\mathcal{I}_D$; flatness of
$g$ is not needed for the closed subscheme, and the identification is
exact because $g^*$ is right exact), and the pullback of a dual is the
dual of the pullback:
$g^*(\mathcal{I}_D^\vee)=\mathcal{H}om(g^*\mathcal{I}_D,\mathcal{O}_Y)$ (both are invertible
and the canonical map is an isomorphism; check locally after a
trivialization of $\mathcal{I}_D$). Hence
$\mathcal{O}_Y(D_Y)=(\mathcal{I}_{D_Y})^\vee=(g^*\mathcal{I}_D)^\vee=g^*(\mathcal{I}_D^\vee)=g^*\mathcal{O}_S(D)$.
