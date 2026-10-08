+++
id = "lem-wf-internal-hom-weil"
kind = "lemma"
title = "Internal Hom of Weil complexes"
order = 2571
uses = ["def-wf-internal-hom", "def-wf-weil-category", "lem-wf-tensor-weil"]
+++
The construction of [def-wf-internal-hom] restricts to an exact
bifunctor

$$
R\operatorname{Hom}_E(-,-):\mathrm{WeilD}(X_0,E)^{\mathrm{op}}\times
\mathrm{WeilD}(X_0,E)\to\mathrm{WeilD}(X_0,E),
$$

the displayed conjugation being an isomorphism for every pair of Weil
complexes.

## Proof

The pullback compatibility of [def-wf-internal-hom]
$\Phi_X^*R\mathcal Hom_E(K,L)\cong R\mathcal Hom_E(\Phi_X^*K,\Phi_X^*L)$ is the naturality of the
derived internal Hom in both variables (exactness of
$\Phi_X^*$), and the composite with
$R\mathcal Hom_E(\varphi_K^{-1},\varphi_L)$ is an isomorphism: the
two Frobenius isomorphisms make the composite a Weil datum, and the
cocycle condition follows as in
[lem-wf-tensor-weil].
