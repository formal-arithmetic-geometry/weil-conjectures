+++
id = "def-sp-left-exact-additive"
kind = "definition"
title = "Additive left exact functors and right derived functors"
order = 501
uses = ["def-sp-abelian", "def-sp-injective-resolutions"]
+++
Let $\mathcal A,\mathcal B$ be abelian categories [def-sp-abelian]. A functor
$v:\mathcal A\to\mathcal B$ is *additive* if it preserves finite products
(equivalently finite biproducts); it is *left exact* if it is additive and
preserves kernels. Suppose that $\mathcal A$ has enough injectives. For a
left exact additive functor $v$ and an object $X\in\mathcal A$, the *right
derived functors* $R^nv$ ($n\geq0$) are defined via injective resolutions
[def-sp-injective-resolutions]: for an injective resolution $X\to I^\bullet$,

$$
 R^nv(X):=\mathcal H^n(v(I^\bullet)),
$$

the independence of the choice and the identification $R^0v=v$ being the
well-definedness lemma below.
