+++
id = "lem-wf-tensor-weil"
kind = "lemma"
title = "Tensor product of Weil complexes"
order = 2569
uses = ["def-wf-tensor-product", "def-wf-weil-category"]
+++
The construction of [def-wf-tensor-product] restricts to an exact
bifunctor

$$
-\otimes^L_E-:\mathrm{WeilD}(X_0,E)\times\mathrm{WeilD}(X_0,E)
\longrightarrow\mathrm{WeilD}(X_0,E).
$$

## Proof

For Weil complexes $(K,\varphi_K)$, $(L,\varphi_L)$, the arrow
$\varphi_K\otimes\varphi_L$ is the tensor of the two Frobenius
isomorphisms, hence an isomorphism satisfying the Weil-cocycle
condition by the functoriality of the construction of
[def-wf-tensor-product]; the bifunctoriality is that of the
ambient derived tensor.
