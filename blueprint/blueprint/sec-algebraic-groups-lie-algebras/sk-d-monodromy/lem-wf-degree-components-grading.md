+++
id = "lem-wf-degree-components-grading"
kind = "lemma"
title = "The degree components multiply by degree"
order = 2509
uses = ["def-wf-arithmetic-monodromy-extension", "def-wf-degree-components", "lem-wf-arith-extension-group"]
+++
In the situation of [def-wf-degree-components], for all
$m,n\in\mathbf Z$ one has

$$
G^{[m]}G^{[n]}=G^{[m+n]},
\qquad (G^{[m]})^{-1}=G^{[-m]},
$$

so that the subsets $G^{[m]}$ are the fibres
$\deg_G^{-1}(m)$ of the degree map of
[def-wf-arithmetic-monodromy-extension] and form a
$\mathbf Z$-grading of $G_{\mathrm{arith}}(\rho)$.

## Proof

By [lem-wf-arith-extension-group] the displayed multiplication of
[def-wf-arithmetic-monodromy-extension] makes
$G_{\mathrm{arith}}(\rho)$ a group whose degree map $\deg_G$ is a
homomorphism, and $G^{[m]}=\deg_G^{-1}(m)$ by
[def-wf-degree-components]. Hence the product of an element of
$G^{[m]}$ with one of $G^{[n]}$ has degree $m+n$ and so lies in
$G^{[m+n]}$, while conversely every $(h,m+n)\in G^{[m+n]}$ equals
$(h,m)(1,n)$ with $(h,m)\in G^{[m]}$ and $(1,n)\in G^{[n]}$; this
gives the first identity. Inversion preserves the degree by the same
homomorphism property, so $(G^{[m]})^{-1}\subseteq G^{[-m]}$, and
applying this containment with $-m$ in place of $m$ and taking
inverses gives the reverse containment.
