+++
id = "sk-prop-rootpurity"
kind = "section"
title = "Reciprocal roots have the weight-$i$ absolute value"
order = 2895
lean = ["AlgebraicGeometry.WeilRiemannHypothesis", "Polynomial.IsPureOfWeight"]
uses = ["sk-def-cohfamily", "sk-def-roots", "sk-input-weights"]
+++
*Proposition (sketch).*

In the situation of [sk-def-cohfamily], for every $0\le i\le2d$ every
reciprocal root $\alpha\in\Qlb$ of $P_{i,\ell}$ satisfies

$$
|\iota(\alpha)|=q^{i/2}.
$$

## Proof

Over $\Qlb$ the polynomial $P_{i,\ell}(T)=\det(1-TF_{i,\ell})$ factors as
$\prod_\beta(1-\beta T)$, the product over the eigenvalues $\beta$ of
$F_{i,\ell}$ on $V_{i,\ell}=H^{i}(X,\Ql)$ counted with multiplicity. So in
the convention of [sk-def-roots] the reciprocal roots of $P_{i,\ell}$ (the
roots of $P_{i,\ell}^{\#}(U)=\prod_\beta(U-\beta)$) are the eigenvalues
$\beta$ themselves, while the ordinary roots of $P_{i,\ell}$ are their
inverses $\beta^{-1}$. By [sk-input-weights] (4)–(5) the space
$V_{i,\ell}$ is $\iota$-pure of weight $i$: every eigenvalue $\beta$
satisfies $|\iota(\beta)|=q^{i/2}$. Hence every reciprocal root
$\alpha=\beta$ has $|\iota(\alpha)|=q^{i/2}$ (whereas the ordinary roots
have $|\iota(\beta^{-1})|=q^{-i/2}$; for $H^{2}(\mathbf P^{1})$ the two
values are $q$ and $q^{-1}$).

Uses: [sk-def-cohfamily], [sk-def-roots], [sk-input-weights]
